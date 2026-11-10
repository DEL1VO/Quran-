#!/usr/bin/env python3
"""
Telegram-бот «КОРАН»
 - /start: приветствие + Бисмиллях (арабский)
 - Выбрать суру: список по 5 кнопок, «Назад / Далее»
 - Поиск суры: по номеру (1-114) или названию латиницей
 - PDF суры (арабский + английская транскрипция) с прогрессом в % и временем
 - Каждые 30 минут: дуа или аят (арабский, транскрипция, перевод)

Запуск:  BOT_TOKEN=... python bot.py
"""
import asyncio
import datetime as dt
import hashlib
import hmac
import json
import logging
import os
import random
import re
import threading
import time
import urllib.request
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qsl, quote
from zoneinfo import ZoneInfo

from fpdf import FPDF
from fpdf.enums import XPos, YPos
from telegram import InlineKeyboardButton as Btn
from telegram import (InlineKeyboardMarkup, KeyboardButton, MenuButtonWebApp,
                      ReplyKeyboardMarkup, Update, WebAppInfo)
from telegram.error import BadRequest, Forbidden, TelegramError
from telegram.ext import (Application, CallbackQueryHandler, CommandHandler,
                          ContextTypes, MessageHandler, filters)

logging.basicConfig(format="%(asctime)s %(levelname)s %(message)s", level=logging.INFO)
log = logging.getLogger("quran-bot")

BASE = Path(__file__).resolve().parent
DATA_DIR = BASE / "data"
FONT_DIR = BASE / "fonts"
PDF_DIR = BASE / "pdf_cache"
SUBS_FILE = DATA_DIR / "subscribers.json"
EXTRA_FILE = DATA_DIR / "extra_duas.json"
REGION_FILE = DATA_DIR / "regions.json"

API = "https://api.alquran.cloud/v1"
# Адрес мини-приложения: домен проекта на bothost (бот сам отдаёт index.html).
# Можно переопределить переменной окружения MINIAPP_URL.
MINIAPP_URL = os.environ.get("MINIAPP_URL", "https://bot-1794203722-4185-idievvv.bothost.tech")
# арабский текст (Усмани), английская транскрипция, русский перевод (Кулиев)
EDITIONS = {"ar": "quran-uthmani", "tr": "en.transliteration", "ru": "ru.kuliev"}

FONT_URLS = {
    "amiri": "https://github.com/google/fonts/raw/main/ofl/amiri/Amiri-Regular.ttf",
    "amiri_b": "https://github.com/google/fonts/raw/main/ofl/amiri/Amiri-Bold.ttf",
    "amiri_q": "https://github.com/google/fonts/raw/main/ofl/amiriquran/AmiriQuran-Regular.ttf",
}

PER_PAGE = 5
BROADCAST_SECONDS = 30 * 60
BISMILLAH_AR = "بِسْمِ ٱللَّهِ ٱلرَّحْمَٰنِ ٱلرَّحِيمِ"

WELCOME = (
    "🕌 Добро пожаловать в КОРАН\n\n"
    "Во имя Аллаха, Милостивого, Милосердного, мы начинаем.\n\n"
    f"{BISMILLAH_AR}\n\n"
    "Каждые 30 минут я буду присылать дуа или аят: арабский текст, "
    "чтение и перевод. Остановить: /stop\n\n"
    "🕌 Нажмите «Регион», чтобы получать время намаза с дуа."
)

# Дуа из Корана: (сура, аят_от, аят_до). Тексты берутся из базы, не набираются вручную.
DUA_REFS = [
    (1, 6, 7), (2, 127, 128), (2, 201, 201), (2, 250, 250), (2, 286, 286),
    (3, 8, 8), (3, 16, 16), (3, 26, 27), (3, 38, 38), (3, 53, 53), (3, 147, 147),
    (3, 191, 194), (5, 114, 114), (7, 23, 23), (7, 89, 89), (7, 126, 126),
    (7, 151, 151), (9, 129, 129), (10, 85, 86), (11, 47, 47), (12, 101, 101),
    (14, 40, 41), (17, 24, 24), (17, 80, 80), (18, 10, 10), (20, 25, 28),
    (20, 114, 114), (21, 83, 83), (21, 87, 87), (21, 89, 89), (23, 97, 98),
    (23, 118, 118), (25, 65, 66), (25, 74, 74), (26, 83, 85), (27, 19, 19),
    (28, 16, 16), (28, 24, 24), (29, 30, 30), (37, 100, 100), (40, 7, 9),
    (46, 15, 15), (54, 10, 10), (59, 10, 10), (60, 4, 5), (66, 8, 8),
    (71, 28, 28), (113, 1, 5), (114, 1, 6),
]

# Чтецы (аудио берётся с mp3quran.net). match: список вариантов, в каждом
# все подстроки должны входить в арабское имя чтеца (пробелы не учитываются).
RECITERS = [
    {"key": "dosari", "label": "Ясир ад-Досари", "match": [["الدوسري"]]},
    {"key": "malik", "label": "Абдуллах аль-Малик",
     "match": [["عبدالله", "الملك"], ["عبدالله", "ملك"]]},
]
REC_API_URL = "https://www.mp3quran.net/api/v3/reciters?language=ar"
_REC_LOCK = threading.Lock()
_REC_DATA: list | None = None

# ----------------------------------------------------------------- данные
META: list[dict] = []
AR: dict[int, list[str]] = {}
TR: dict[int, list[str]] = {}
RU: dict[int, list[str]] = {}
EXTRA: list[dict] = []
AYAH_POOL: list[tuple[int, int]] = []

_MARKS = re.compile(r"[\u0640\u064B-\u065F\u0670\u06D6-\u06ED]")


def http_get(url: str, timeout: int = 180) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "quran-bot/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def _strip_bismillah(sura: int, ar: list[str], tr: list[str]) -> None:
    """В некоторых источниках бисмиллях приклеен к 1-му аяту суры. Убираем."""
    if sura in (1, 9):
        return
    w = ar[0].split()
    if len(w) > 4 and _MARKS.sub("", w[0]) == "بسم":
        ar[0] = " ".join(w[4:])
    w = tr[0].split()
    if len(w) > 4 and w[0].lower().startswith("bismi"):
        tr[0] = " ".join(w[4:])


def load_data() -> None:
    global META, AR, TR, RU, EXTRA, AYAH_POOL
    DATA_DIR.mkdir(exist_ok=True)
    cache = DATA_DIR / "quran_data.json"
    if not cache.exists():
        log.info("Скачиваю данные Корана (один раз)...")
        out = {"meta": [], "ar": {}, "tr": {}, "ru": {}}
        for key, edition in EDITIONS.items():
            payload = json.loads(http_get(f"{API}/quran/{edition}"))
            for s in payload["data"]["surahs"]:
                n = s["number"]
                out[key][str(n)] = [a["text"].strip() for a in s["ayahs"]]
                if key == "ar":
                    out["meta"].append({
                        "n": n, "ar": s["name"], "en": s["englishName"],
                        "tn": s["englishNameTranslation"],
                        "type": s["revelationType"], "count": len(s["ayahs"]),
                    })
        if len(out["meta"]) != 114:
            raise RuntimeError("Получено не 114 сур, проверьте доступ к api.alquran.cloud")
        cache.write_text(json.dumps(out, ensure_ascii=False), encoding="utf-8")

    data = json.loads(cache.read_text(encoding="utf-8"))
    META = sorted(data["meta"], key=lambda m: m["n"])
    AR = {int(k): v for k, v in data["ar"].items()}
    TR = {int(k): v for k, v in data["tr"].items()}
    RU = {int(k): v for k, v in data["ru"].items()}
    for n in AR:
        _strip_bismillah(n, AR[n], TR[n])

    AYAH_POOL = [
        (s, a) for s in AR for a in range(1, len(AR[s]) + 1)
        if len(AR[s][a - 1]) + len(TR[s][a - 1]) + len(RU[s][a - 1]) < 2800
    ]
    if EXTRA_FILE.exists():
        try:
            EXTRA = json.loads(EXTRA_FILE.read_text(encoding="utf-8"))
        except Exception:
            log.exception("extra_duas.json не читается")
    log.info("Данные загружены: %d сур, %d аятов в пуле, %d своих дуа",
             len(META), len(AYAH_POOL), len(EXTRA))


def ensure_fonts() -> dict[str, Path]:
    FONT_DIR.mkdir(exist_ok=True)
    paths = {}
    for key, url in FONT_URLS.items():
        p = FONT_DIR / url.rsplit("/", 1)[1]
        if not p.exists():
            try:
                log.info("Скачиваю шрифт %s", p.name)
                p.write_bytes(http_get(url))
            except Exception:
                log.warning("Не удалось скачать %s", p.name)
        paths[key] = p
    if not paths["amiri"].exists() or not paths["amiri_b"].exists():
        raise SystemExit("Положите Amiri-Regular.ttf и Amiri-Bold.ttf в папку fonts/")
    if not paths["amiri_q"].exists():
        paths["amiri_q"] = paths["amiri"]
    return paths


FONTS: dict[str, Path] = {}

# ----------------------------------------------------------------- PDF
CREAM, GOLD, GREEN = (253, 250, 242), (176, 141, 60), (24, 84, 64)
GOLD_LIGHT, INK, TRC, LINE = (240, 217, 150), (25, 25, 25), (55, 95, 80), (222, 212, 185)


class QuranPDF(FPDF):
    def __init__(self, title: str):
        super().__init__(format="A4")
        self.doc_title = title
        self.set_margins(22, 22, 22)
        self.set_auto_page_break(True, margin=22)
        self.add_font("Amiri", "", str(FONTS["amiri"]))
        self.add_font("Amiri", "B", str(FONTS["amiri_b"]))
        self.add_font("AmiriQ", "", str(FONTS["amiri_q"]))
        self.set_text_shaping(True)  # корректная арабская графика (HarfBuzz)

    def header(self):
        self.set_fill_color(*CREAM)
        self.rect(0, 0, 210, 297, style="F")
        self.set_draw_color(*GOLD)
        self.set_line_width(1.0)
        self.rect(8, 8, 194, 281)
        self.set_draw_color(*GREEN)
        self.set_line_width(0.3)
        self.rect(10.5, 10.5, 189, 276)
        self.set_fill_color(*GOLD)
        for cx, cy in ((8, 8), (202, 8), (8, 289), (202, 289)):
            self.polygon([(cx, cy - 3.5), (cx + 3.5, cy), (cx, cy + 3.5), (cx - 3.5, cy)], style="F")
        if self.page_no() > 1:
            self.set_font("Amiri", "", 9)
            self.set_text_color(*GOLD)
            self.set_xy(22, 13.5)
            self.cell(166, 5, self.doc_title, align="C")
        self.set_xy(self.l_margin, self.t_margin)

    def footer(self):
        self.set_y(-17)
        self.set_font("Amiri", "", 9)
        self.set_text_color(*GOLD)
        self.cell(0, 6, f"—  {self.page_no()}  —", align="C")


def pdf_path(n: int) -> Path:
    return PDF_DIR / f"surah_{n:03d}.pdf"


def pdf_filename(n: int) -> str:
    return f"Surah_{n:03d}_{re.sub(r'[^A-Za-z0-9]+', '_', META[n - 1]['en']).strip('_')}.pdf"


def build_pdf(n: int, progress) -> Path:
    """Собирает PDF суры n. progress(pct) вызывается из рабочего потока."""
    PDF_DIR.mkdir(exist_ok=True)
    out = pdf_path(n)
    if out.exists():
        progress(100)
        return out

    m = META[n - 1]
    ar_list, tr_list = AR[n], TR[n]
    total = len(ar_list)
    progress(3)

    pdf = QuranPDF(f"Surah {n} · {m['en']}")
    pdf.add_page()

    # --- баннер с названием суры
    pdf.set_fill_color(*GREEN)
    pdf.set_draw_color(*GOLD)
    pdf.set_line_width(0.8)
    pdf.rect(22, 24, 166, 46, style="DF", round_corners=True, corner_radius=5)
    pdf.set_text_color(*GOLD_LIGHT)
    pdf.set_font("AmiriQ", "", 34)
    pdf.set_xy(22, 27)
    pdf.cell(166, 20, m["ar"], align="C")
    pdf.set_font("Amiri", "B", 15)
    pdf.set_text_color(255, 255, 255)
    pdf.set_xy(22, 50)
    pdf.cell(166, 8, f"{m['en']}  ·  {m['tn']}", align="C")
    pdf.set_font("Amiri", "", 10)
    pdf.set_text_color(*GOLD_LIGHT)
    pdf.set_xy(22, 59)
    pdf.cell(166, 6, f"Surah {n}  ·  {m['type']}  ·  {total} ayahs", align="C")

    pdf.set_y(78)
    if n not in (1, 9):
        pdf.set_text_color(*INK)
        pdf.set_font("AmiriQ", "", 24)
        pdf.cell(0, 16, BISMILLAH_AR, align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    y = pdf.get_y() + 3
    pdf.set_draw_color(*GOLD)
    pdf.set_line_width(0.4)
    pdf.line(40, y, 101, y)
    pdf.line(109, y, 170, y)
    pdf.set_fill_color(*GOLD)
    pdf.polygon([(105, y - 2.2), (107.2, y), (105, y + 2.2), (102.8, y)], style="F")
    pdf.set_y(y + 8)

    # --- аяты
    text_x, text_w = 35, 210 - 22 - 35
    for i, (ar, tr) in enumerate(zip(ar_list, tr_list), start=1):
        if pdf.get_y() > 297 - 22 - 55:
            pdf.add_page()
        y0 = pdf.get_y()
        pdf.set_draw_color(*GOLD)
        pdf.set_fill_color(*CREAM)
        pdf.set_line_width(0.5)
        pdf.ellipse(22, y0 + 2, 9, 9, style="DF")
        pdf.set_font("Amiri", "B", 8)
        pdf.set_text_color(*GREEN)
        pdf.set_xy(22, y0 + 2)
        pdf.cell(9, 9, str(i), align="C")

        pdf.set_font("AmiriQ", "", 21)
        pdf.set_text_color(*INK)
        pdf.set_x(text_x)
        pdf.multi_cell(text_w, 12, ar, align="R", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        pdf.set_font("Amiri", "", 10.5)
        pdf.set_text_color(*TRC)
        pdf.set_x(text_x)
        pdf.multi_cell(text_w, 5.6, tr, align="L", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

        pdf.ln(2)
        pdf.set_draw_color(*LINE)
        pdf.set_line_width(0.2)
        yy = pdf.get_y()
        pdf.line(text_x, yy, 188, yy)
        pdf.ln(4)
        progress(5 + int(90 * i / total))

    progress(97)
    tmp = out.with_suffix(".tmp")
    pdf.output(str(tmp))
    os.replace(tmp, out)
    progress(100)
    return out


# ----------------------------------------------------------------- подписчики
SUBS: set[int] = set()


def load_subs() -> None:
    if SUBS_FILE.exists():
        try:
            SUBS.update(json.loads(SUBS_FILE.read_text()))
        except Exception:
            log.exception("subscribers.json не читается")


def save_subs() -> None:
    DATA_DIR.mkdir(exist_ok=True)
    SUBS_FILE.write_text(json.dumps(sorted(SUBS)))


# ----------------------------------------------------------------- дуа / аяты
def _range_text(s: int, a1: int, a2: int) -> tuple[str, str, str]:
    sl = slice(a1 - 1, a2)
    return " ".join(AR[s][sl]), " ".join(TR[s][sl]), " ".join(RU[s][sl])


def _format(header: str, place: str, ar: str, tr: str, ru: str) -> str:
    return (f"{header}\n{place}\n\n{ar}\n\n🔤 Чтение:\n{tr}\n\n🇷🇺 Перевод:\n{ru}")[:4000]


def random_message() -> str:
    kinds, weights = ["dua", "ayah"], [5, 4]
    if EXTRA:
        kinds.append("extra")
        weights.append(1)
    kind = random.choices(kinds, weights)[0]
    if kind == "extra":
        d = random.choice(EXTRA)
        return _format(f"🤲 {d.get('title', 'Дуа')}", d.get("source", ""),
                       d.get("ar", ""), d.get("tr", ""), d.get("ru", ""))
    if kind == "dua":
        s, a1, a2 = random.choice(DUA_REFS)
        header = "🤲 Дуа из Корана"
    else:
        s, a1 = random.choice(AYAH_POOL)
        a2 = a1
        header = "📖 Аят Корана"
    ref = f"{s}:{a1}" if a1 == a2 else f"{s}:{a1}-{a2}"
    ar, tr, ru = _range_text(s, a1, a2)
    return _format(header, f"📍 Сура {META[s - 1]['en']} ({ref})", ar, tr, ru)


async def broadcast(context: ContextTypes.DEFAULT_TYPE) -> None:
    if not SUBS:
        return
    text = random_message()
    for chat_id in list(SUBS):
        try:
            await context.bot.send_message(chat_id, text)
        except Forbidden:
            SUBS.discard(chat_id)
            save_subs()
        except TelegramError as e:
            log.warning("send to %s failed: %s", chat_id, e)
        await asyncio.sleep(0.05)


# ----------------------------------------------------------------- клавиатуры
BTN_LIST = "📖 Выбрать суру"
BTN_SEARCH = "🔎 Поиск суры"
BTN_CHECK = "🎙 Проверить себя"
BTN_REGION = "🕌 Регион / время намаза"
CHECK_TEXT = ("🎙 Проверьте себя в правильном чтении сур\n\n"
              "Нажмите «Проверить», выберите суру и читайте вслух: аяты проявятся на "
              "странице, ошибки подсветятся, а в конце вы увидите процент и совет.")


def bottom_markup() -> ReplyKeyboardMarkup:
    """Кнопки, закреплённые внизу экрана."""
    return ReplyKeyboardMarkup(
        [[KeyboardButton(BTN_LIST), KeyboardButton(BTN_SEARCH)],
         [KeyboardButton(BTN_CHECK, web_app=WebAppInfo(url=MINIAPP_URL))],
         [KeyboardButton(BTN_REGION)]],
        resize_keyboard=True, is_persistent=True,
        input_field_placeholder="Номер суры или название")


def check_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[Btn("✅ Проверить", web_app=WebAppInfo(url=MINIAPP_URL))],
                                 [Btn("🏠 Меню", callback_data="menu")]])


def main_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [Btn("📖 Выбрать суру", callback_data="list:0"),
         Btn("🔎 Поиск суры", callback_data="search")],
        [Btn("🎙 Проверить себя", callback_data="check")],
        [Btn("🕌 Регион / время намаза", callback_data="reg")]])


def menu_only() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[Btn("🏠 Меню", callback_data="menu")]])


def after_pdf_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[Btn("📖 Выбрать суру", callback_data="list:0"),
                                  Btn("🔎 Поиск", callback_data="search")],
                                 [Btn("🏠 Меню", callback_data="menu")]])


def list_markup(page: int) -> InlineKeyboardMarkup:
    pages = (len(META) + PER_PAGE - 1) // PER_PAGE
    rows = [[Btn(f"{m['n']}. {m['en']} — {m['count']}", callback_data=f"card:{m['n']}")]
            for m in META[page * PER_PAGE:(page + 1) * PER_PAGE]]
    nav = []
    if page > 0:
        nav.append(Btn("◀️ Назад", callback_data=f"list:{page - 1}"))
    nav.append(Btn(f"{page + 1}/{pages}", callback_data="noop"))
    if page < pages - 1:
        nav.append(Btn("Далее ▶️", callback_data=f"list:{page + 1}"))
    rows.append(nav)
    rows.append([Btn("🏠 Меню", callback_data="menu")])
    return InlineKeyboardMarkup(rows)


def card_text(n: int) -> str:
    m = META[n - 1]
    kind = "Мекканская" if m["type"] == "Meccan" else "Мединская"
    return (f"📖 Сура {n}: {m['en']}\n{m['ar']}\n«{m['tn']}»\n"
            f"{kind} · аятов: {m['count']}")


def card_markup(n: int) -> InlineKeyboardMarkup:
    rows = [[Btn("📄 Скачать PDF", callback_data=f"pdf:{n}")]]
    rows += [[Btn(f"🎧 {r['label']}", callback_data=f"aud:{r['key']}:{n}")] for r in RECITERS]
    rows.append([Btn("📖 Список сур", callback_data="list:0"), Btn("🏠 Меню", callback_data="menu")])
    return InlineKeyboardMarkup(rows)


async def show(q, text: str, markup: InlineKeyboardMarkup) -> None:
    """Редактирует сообщение; если оно с файлом (редактировать нельзя), шлёт новое."""
    try:
        await q.message.edit_text(text, reply_markup=markup)
    except BadRequest:
        await q.message.reply_text(text, reply_markup=markup)


# ----------------------------------------------------------------- обработчики
async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    SUBS.add(update.effective_chat.id)
    save_subs()
    await update.message.reply_text(WELCOME, reply_markup=main_markup())
    await update.message.reply_text("👇 Кнопки меню всегда внизу, под рукой.",
                                    reply_markup=bottom_markup())


async def cmd_stop(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    SUBS.discard(update.effective_chat.id)
    save_subs()
    await update.message.reply_text("Рассылка остановлена. Чтобы включить снова: /start")


async def cmd_dua(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(random_message())


def fmt_time(sec: float) -> str:
    m, s = divmod(int(sec), 60)
    return f"{m:02d}:{s:02d}"


def progress_text(name: str, pct: int, started: float) -> str:
    filled = pct // 10
    return (f"⏳ Готовлю PDF: {name}\n\n{'█' * filled}{'░' * (10 - filled)} {pct}%\n"
            f"⏱ Прошло: {fmt_time(time.monotonic() - started)} (мин:сек)")


PDF_SEM = asyncio.Semaphore(2)  # не больше 2 сборок одновременно


async def make_pdf(q, ctx: ContextTypes.DEFAULT_TYPE, n: int) -> None:
    m = META[n - 1]
    chat_id = q.message.chat_id
    started = time.monotonic()
    state = {"pct": 0}
    msg = await ctx.bot.send_message(chat_id, progress_text(m["en"], 0, started))

    async def runner() -> Path:
        async with PDF_SEM:
            return await asyncio.to_thread(build_pdf, n, lambda p: state.update(pct=p))

    task = asyncio.create_task(runner())
    last = ""
    while not task.done():
        await asyncio.wait({task}, timeout=1.5)
        text = progress_text(m["en"], min(state["pct"], 99), started)
        if text != last and not task.done():
            try:
                await msg.edit_text(text)
                last = text
            except TelegramError:
                pass
    try:
        path = task.result()
    except Exception as e:
        log.exception("PDF error")
        await msg.edit_text(f"❌ Не удалось собрать PDF: {e}")
        return

    await msg.edit_text(f"✅ Готово! {m['en']} — 100%\n⏱ Время: {fmt_time(time.monotonic() - started)}")
    with open(path, "rb") as f:
        await ctx.bot.send_document(
            chat_id, document=f, filename=pdf_filename(n),
            caption=f"📖 Сура {n}: {m['en']}\n{m['ar']}\nАрабский текст + английская транскрипция",
            reply_markup=after_pdf_markup())


# ----------------------------------------------------------------- намаз
PRAYERS = [("Fajr", "Фаджр"), ("Dhuhr", "Зухр"), ("Asr", "Аср"),
           ("Maghrib", "Магриб"), ("Isha", "Иша")]

# (название по-русски, название для API[, мазхаб аср: 1 ханафитский, 0 остальные])
COUNTRIES = {
    "tj": {"name": "🇹🇯 Таджикистан", "country": "Tajikistan", "method": 3, "school": 1,
           "cities": [("Душанбе", "Dushanbe"), ("Худжанд", "Khujand"), ("Бохтар", "Bokhtar"),
                      ("Куляб", "Kulob"), ("Истаравшан", "Istaravshan"),
                      ("Пенджикент", "Panjakent"), ("Хорог", "Khorog"),
                      ("Турсунзода", "Tursunzoda")]},
    "uz": {"name": "🇺🇿 Узбекистан", "country": "Uzbekistan", "method": 3, "school": 1,
           "cities": [("Ташкент", "Tashkent"), ("Самарканд", "Samarkand"), ("Бухара", "Bukhara"),
                      ("Андижан", "Andijan"), ("Наманган", "Namangan"), ("Фергана", "Fergana"),
                      ("Коканд", "Kokand"), ("Нукус", "Nukus"), ("Карши", "Karshi"),
                      ("Термез", "Termez"), ("Ургенч", "Urgench"), ("Навои", "Navoiy")]},
    "ru": {"name": "🇷🇺 Россия", "country": "Russia", "method": 14, "school": 1,
           "cities": [("Москва", "Moscow"), ("Санкт-Петербург", "Saint Petersburg"),
                      ("Казань", "Kazan"), ("Уфа", "Ufa"), ("Нижний Новгород", "Nizhny Novgorod"),
                      ("Екатеринбург", "Yekaterinburg"), ("Новосибирск", "Novosibirsk"),
                      ("Самара", "Samara"), ("Челябинск", "Chelyabinsk"), ("Пермь", "Perm"),
                      ("Омск", "Omsk"), ("Тюмень", "Tyumen"), ("Краснодар", "Krasnodar"),
                      ("Набережные Челны", "Naberezhnye Chelny"),
                      ("Махачкала", "Makhachkala", 0), ("Грозный", "Grozny", 0)]},
}

USER_REG: dict[int, dict] = {}
_TIMES: dict[tuple, dict] = {}
_FAILED: dict[tuple, float] = {}
_SENT: set[tuple] = set()


def load_regions() -> None:
    if REGION_FILE.exists():
        try:
            USER_REG.update({int(k): v for k, v in json.loads(REGION_FILE.read_text()).items()})
        except Exception:
            log.exception("regions.json не читается")


def save_regions() -> None:
    DATA_DIR.mkdir(exist_ok=True)
    REGION_FILE.write_text(json.dumps(USER_REG, ensure_ascii=False))


def fetch_timings(city: str, country: str, method: int, school: int,
                  date: dt.date | None) -> tuple[dict, str]:
    """Время пяти намазов и часовой пояс через api.aladhan.com."""
    path = "timingsByCity" + (f"/{date:%d-%m-%Y}" if date else "")
    url = (f"https://api.aladhan.com/v1/{path}?city={quote(city)}"
           f"&country={quote(country)}&method={method}&school={school}")
    d = json.loads(http_get(url, timeout=30))
    if d.get("code") != 200:
        raise ValueError(f"Aladhan: {d}")
    out = {}
    for key, _ in PRAYERS:
        mt = re.search(r"(\d{1,2}):(\d{2})", d["data"]["timings"][key])
        out[key] = (int(mt.group(1)), int(mt.group(2)))
    return out, d["data"]["meta"]["timezone"]


def dua_block() -> str:
    s, a1, a2 = random.choice(DUA_REFS)
    ref = f"{s}:{a1}" if a1 == a2 else f"{s}:{a1}-{a2}"
    ar, tr, ru = _range_text(s, a1, a2)
    return _format("🤲 Дуа из Корана", f"📍 Сура {META[s - 1]['en']} ({ref})", ar, tr, ru)


async def apply_region(chat_id: int, label: str, city: str, country: str,
                       method: int, school: int) -> str | None:
    try:
        t, tz = await asyncio.to_thread(fetch_timings, city, country, method, school, None)
    except Exception:
        log.exception("Не удалось получить время намаза для %s, %s", city, country)
        return None
    USER_REG[chat_id] = {"label": label, "city": city, "country": country,
                         "method": method, "school": school, "tz": tz}
    save_regions()
    lines = "\n".join(f"• {ru}: {t[k][0]:02d}:{t[k][1]:02d}" for k, ru in PRAYERS)
    return (f"✅ Регион: {label}\n🕌 Время намаза сегодня (по времени региона):\n{lines}\n\n"
            "В каждое время намаза пришлю сообщение с дуа. "
            "Время расчётное и может отличаться на несколько минут от календаря вашей мечети.")


async def prayer_tick(context: ContextTypes.DEFAULT_TYPE) -> None:
    if not USER_REG:
        return
    now_utc = dt.datetime.now(dt.timezone.utc)
    for chat_id, reg in list(USER_REG.items()):
        try:
            now = now_utc.astimezone(ZoneInfo(reg["tz"]))
        except Exception:
            continue
        day = now.date().isoformat()
        key = (reg["city"], reg["country"], reg["method"], reg["school"], day)
        times = _TIMES.get(key)
        if times is None:
            if time.monotonic() - _FAILED.get(key, -999) < 600:
                continue
            try:
                times, _ = await asyncio.to_thread(
                    fetch_timings, reg["city"], reg["country"], reg["method"], reg["school"], now.date())
                _TIMES[key] = times
            except Exception:
                log.exception("Время намаза не получено: %s", key)
                _FAILED[key] = time.monotonic()
                continue
        for name, ru in PRAYERS:
            h, m = times[name]
            diff = (now - now.replace(hour=h, minute=m, second=0, microsecond=0)).total_seconds()
            sent_key = (chat_id, day, name)
            if 0 <= diff < 180 and sent_key not in _SENT:
                _SENT.add(sent_key)
                text = (f"🕌 Время намаза: {ru} — {h:02d}:{m:02d}\n📍 {reg['label']}\n\n"
                        + dua_block())[:4090]
                try:
                    await context.bot.send_message(chat_id, text)
                except Forbidden:
                    USER_REG.pop(chat_id, None)
                    save_regions()
                    break
                except TelegramError as e:
                    log.warning("prayer msg to %s failed: %s", chat_id, e)
    if len(_SENT) > 5000:
        _SENT.clear()
    if len(_TIMES) > 300:
        _TIMES.clear()


def region_text(chat_id: int) -> str:
    reg = USER_REG.get(chat_id)
    cur = f"Сейчас выбран: {reg['label']}" if reg else "Регион не выбран."
    return f"🌍 Выберите страну, затем город, чтобы получать время намаза с дуа.\n\n{cur}"


def countries_markup(chat_id: int) -> InlineKeyboardMarkup:
    rows = [[Btn(c["name"], callback_data=f"rc:{k}")] for k, c in COUNTRIES.items()]
    rows.append([Btn("✍️ Другой город", callback_data="rother")])
    if chat_id in USER_REG:
        rows.append([Btn("🔕 Отключить время намаза", callback_data="roff")])
    rows.append([Btn("🏠 Меню", callback_data="menu")])
    return InlineKeyboardMarkup(rows)


def cities_markup(ck: str) -> InlineKeyboardMarkup:
    cities = COUNTRIES[ck]["cities"]
    rows, row = [], []
    for i, c in enumerate(cities):
        row.append(Btn(c[0], callback_data=f"rcity:{ck}:{i}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([Btn("◀️ Страны", callback_data="reg"), Btn("🏠 Меню", callback_data="menu")])
    return InlineKeyboardMarkup(rows)


async def handle_region_button(q, ctx: ContextTypes.DEFAULT_TYPE, data: str) -> None:
    chat_id = q.message.chat_id
    if data == "reg":
        await show(q, region_text(chat_id), countries_markup(chat_id))
    elif data.startswith("rc:"):
        ck = data.split(":")[1]
        await show(q, f"{COUNTRIES[ck]['name']}: выберите город", cities_markup(ck))
    elif data == "rother":
        ctx.user_data["await_city"] = True
        await show(q, "✍️ Напишите город и страну латиницей через запятую.\n"
                      "Например: Osh, Kyrgyzstan", menu_only())
    elif data == "roff":
        USER_REG.pop(chat_id, None)
        save_regions()
        await show(q, "🔕 Время намаза отключено.", countries_markup(chat_id))
    elif data.startswith("rcity:"):
        _, ck, idx = data.split(":")
        c = COUNTRIES[ck]
        city = c["cities"][int(idx)]
        school = city[2] if len(city) > 2 else c["school"]
        country_ru = c["name"].split(" ", 1)[1]
        await show(q, f"⏳ Загружаю время намаза: {city[0]}...", menu_only())
        res = await apply_region(chat_id, f"{city[0]}, {country_ru}", city[1],
                                 c["country"], c["method"], school)
        await show(q, res or "❌ Не удалось получить время намаза для этого города. "
                             "Выберите другой или введите город вручную.",
                   countries_markup(chat_id) if not res else menu_only())


async def cmd_region(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    cid = update.effective_chat.id
    await update.message.reply_text(region_text(cid), reply_markup=countries_markup(cid))


# ----------------------------------------------------------------- аудио
def _arnorm(s: str) -> str:
    s = _MARKS.sub("", s)
    for a, b in (("أ", "ا"), ("إ", "ا"), ("آ", "ا"), ("ى", "ي"), ("ة", "ه")):
        s = s.replace(a, b)
    return re.sub(r"\s+", "", s)


def _load_rec_api() -> list:
    global _REC_DATA
    with _REC_LOCK:
        if _REC_DATA is None:
            cache = DATA_DIR / "reciters.json"
            if cache.exists():
                _REC_DATA = json.loads(cache.read_text(encoding="utf-8"))
            else:
                _REC_DATA = json.loads(http_get(REC_API_URL))["reciters"]
                DATA_DIR.mkdir(exist_ok=True)
                cache.write_text(json.dumps(_REC_DATA, ensure_ascii=False), encoding="utf-8")
        return _REC_DATA


def resolve_audio(key: str, n: int) -> tuple[str | None, str]:
    """Возвращает (ссылка на mp3, '') или (None, причина)."""
    rec = next(r for r in RECITERS if r["key"] == key)
    found = None
    for item in _load_rec_api():
        name = _arnorm(item["name"])
        if any(all(_arnorm(t) in name for t in alt) for alt in rec["match"]):
            found = item
            break
    if not found:
        return None, (f"Чтец «{rec['label']}» не найден в базе mp3quran.net. "
                      "Выберите другого чтеца.")
    cands = [m for m in found["moshaf"]
             if str(n) in str(m.get("surah_list", "")).split(",")]
    if not cands:
        return None, f"У чтеца «{rec['label']}» нет суры {n} в базе."
    cands.sort(key=lambda m: ("حفص" not in m["name"], "مرتل" not in m["name"]))
    server = cands[0]["server"]
    if not server.endswith("/"):
        server += "/"
    return f"{server}{n:03d}.mp3", ""


def head_size(url: str) -> int | None:
    try:
        req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "quran-bot/1.0"})
        with urllib.request.urlopen(req, timeout=20) as r:
            return int(r.headers.get("Content-Length", 0)) or None
    except Exception:
        return None


async def send_audio(q, ctx: ContextTypes.DEFAULT_TYPE, key: str, n: int) -> None:
    rec = next(r for r in RECITERS if r["key"] == key)
    m = META[n - 1]
    chat_id = q.message.chat_id
    msg = await ctx.bot.send_message(chat_id, f"🔎 Ищу суру {m['en']} в чтении {rec['label']}...")
    try:
        url, err = await asyncio.to_thread(resolve_audio, key, n)
    except Exception as e:
        log.exception("audio lookup")
        await msg.edit_text(f"❌ Не удалось связаться с mp3quran.net: {e}")
        return
    if not url:
        await msg.edit_text(f"❌ {err}", reply_markup=card_markup(n))
        return

    kb = InlineKeyboardMarkup([
        [Btn("▶️ Открыть / скачать MP3", url=url)],
        [Btn("📄 PDF", callback_data=f"pdf:{n}"), Btn("📖 Суры", callback_data="list:0")],
        [Btn("🏠 Меню", callback_data="menu")]])
    size = await asyncio.to_thread(head_size, url)
    if size and size <= 20 * 1024 * 1024:  # Telegram берёт файл по ссылке до 20 МБ
        try:
            await ctx.bot.send_audio(chat_id, audio=url, title=f"{n}. {m['en']}",
                                     performer=rec["label"],
                                     caption=f"🎧 {rec['label']}\nСура {n}: {m['en']} · {m['ar']}",
                                     reply_markup=kb)
            await msg.delete()
            return
        except TelegramError:
            log.exception("send_audio by url failed")
    await msg.edit_text(
        f"🎧 {rec['label']}: сура {n} — {m['en']}\n{m['ar']}\n\n"
        "Файл найден. Нажмите кнопку, чтобы слушать или скачать:", reply_markup=kb)


async def on_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    data = q.data
    await q.answer()
    if data == "noop":
        return
    if data != "rother":
        ctx.user_data.pop("await_city", None)
    if data in ("reg", "roff", "rother") or data.startswith(("rc:", "rcity:")):
        await handle_region_button(q, ctx, data)
        return
    if data == "menu":
        await show(q, WELCOME, main_markup())
    elif data == "check":
        await show(q, CHECK_TEXT, check_markup())
    elif data.startswith("list:"):
        page = int(data.split(":")[1])
        pages = (len(META) + PER_PAGE - 1) // PER_PAGE
        await show(q, f"📖 Выберите суру (страница {page + 1} из {pages}):", list_markup(page))
    elif data == "search":
        await show(q, "🔎 Введите номер суры (1–114) или название латиницей, например: 36 или Yasin",
                   menu_only())
    elif data.startswith("card:"):
        n = int(data.split(":")[1])
        await show(q, card_text(n), card_markup(n))
    elif data.startswith("aud:"):
        _, key, num = data.split(":")
        await send_audio(q, ctx, key, int(num))
    elif data.startswith("pdf:"):
        await make_pdf(q, ctx, int(data.split(":")[1]))


def _norm(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


def find_surahs(query: str) -> list[int]:
    query = query.strip()
    if query.isdigit():
        n = int(query)
        return [n] if 1 <= n <= len(META) else []
    nq = _norm(query)
    if len(nq) < 2:
        return []
    return [m["n"] for m in META if nq in _norm(m["en"]) or nq in _norm(m["tn"])][:8]


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    txt = (update.message.text or "").strip()
    if txt in (BTN_LIST, BTN_SEARCH, BTN_CHECK, BTN_REGION):
        ctx.user_data.pop("await_city", None)
        if txt == BTN_LIST:
            pages = (len(META) + PER_PAGE - 1) // PER_PAGE
            await update.message.reply_text(f"📖 Выберите суру (страница 1 из {pages}):",
                                            reply_markup=list_markup(0))
        elif txt == BTN_SEARCH:
            await update.message.reply_text(
                "🔎 Введите номер суры (1–114) или название латиницей, например: 36 или Yasin",
                reply_markup=menu_only())
        elif txt == BTN_CHECK:
            await update.message.reply_text(CHECK_TEXT, reply_markup=check_markup())
        else:
            cid = update.effective_chat.id
            await update.message.reply_text(region_text(cid), reply_markup=countries_markup(cid))
        return
    if ctx.user_data.get("await_city"):
        parts = [x.strip() for x in (update.message.text or "").split(",")]
        if len(parts) != 2 or not all(parts):
            await update.message.reply_text("Формат: Город, Страна (латиницей). Например: Osh, Kyrgyzstan",
                                            reply_markup=menu_only())
            return
        ctx.user_data.pop("await_city", None)
        cid = update.effective_chat.id
        res = await apply_region(cid, f"{parts[0]}, {parts[1]}", parts[0], parts[1], 3, 1)
        await update.message.reply_text(
            res or "❌ Не нашёл такой город. Проверьте написание (латиницей) и попробуйте снова.",
            reply_markup=menu_only() if res else countries_markup(cid))
        return
    found = find_surahs(update.message.text or "")
    if not found:
        await update.message.reply_text(
            "Не нашёл такую суру. Введите номер от 1 до 114 или название латиницей.",
            reply_markup=menu_only())
    elif len(found) == 1:
        await update.message.reply_text(card_text(found[0]), reply_markup=card_markup(found[0]))
    else:
        rows = [[Btn(f"{n}. {META[n - 1]['en']}", callback_data=f"card:{n}")] for n in found]
        rows.append([Btn("🏠 Меню", callback_data="menu")])
        await update.message.reply_text("Найдено несколько сур, выберите:",
                                        reply_markup=InlineKeyboardMarkup(rows))


async def on_error(update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Ошибка обработчика", exc_info=ctx.error)


TOKEN = ""
_RATE: dict[int, list[float]] = {}


def valid_init_data(init: str) -> int | None:
    """Проверка подписи Telegram WebApp initData. Возвращает id пользователя или None."""
    try:
        pairs = dict(parse_qsl(init, keep_blank_values=True))
        got = pairs.pop("hash", "")
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not got or not hmac.compare_digest(calc, got):
            return None
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            return None
        return int(json.loads(pairs["user"])["id"])
    except Exception:
        return None


def transcribe(audio: bytes, ctype: str) -> str:
    """Распознавание арабской речи через OpenAI (нужен OPENAI_API_KEY)."""
    ctype = ctype.split(";")[0].strip() or "audio/webm"
    ext = next((k for k in ("mp4", "ogg", "wav", "mpeg", "webm") if k in ctype), "webm")
    boundary = "----quran" + uuid.uuid4().hex
    parts = []
    for name, val in (("model", os.environ.get("STT_MODEL", "whisper-1")), ("language", "ar"),
                      ("response_format", "json"), ("temperature", "0")):
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{val}\r\n'.encode())
    parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="file"; '
                  f'filename="a.{ext}"\r\nContent-Type: {ctype}\r\n\r\n').encode() + audio + b"\r\n")
    parts.append(f"--{boundary}--\r\n".encode())
    req = urllib.request.Request(
        "https://api.openai.com/v1/audio/transcriptions", data=b"".join(parts),
        headers={"Authorization": f"Bearer {os.environ['OPENAI_API_KEY']}",
                 "Content-Type": f"multipart/form-data; boundary={boundary}"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read()).get("text", "")


class _PageHandler(BaseHTTPRequestHandler):
    """Отдаёт index.html мини-приложения (порт PORT, по умолчанию 3000) и API распознавания."""

    def _send(self, code: int, body: bytes, ctype: str) -> None:
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?")[0]
        if path in ("/", "/index.html"):
            self._send(200, (BASE / "index.html").read_bytes(), "text/html; charset=utf-8")
        elif path == "/health":
            self._send(200, b"ok", "text/plain")
        elif path == "/api/stt":
            body = json.dumps({"enabled": bool(os.environ.get("OPENAI_API_KEY"))}).encode()
            self._send(200, body, "application/json")
        else:
            self._send(404, b"not found", "text/plain")

    def do_POST(self):
        if self.path.split("?")[0] != "/api/transcribe":
            return self._send(404, b"not found", "text/plain")
        if not os.environ.get("OPENAI_API_KEY"):
            return self._send(503, b'{"error":"disabled"}', "application/json")
        uid = valid_init_data(self.headers.get("X-Init-Data", ""))
        if uid is None:
            return self._send(403, b'{"error":"forbidden"}', "application/json")
        now = time.time()
        hits = [t for t in _RATE.get(uid, []) if now - t < 60]
        if len(hits) >= 20:
            return self._send(429, b'{"error":"too many requests"}', "application/json")
        _RATE[uid] = hits + [now]
        length = int(self.headers.get("Content-Length", "0") or 0)
        if length <= 0 or length > 8_000_000:
            return self._send(413, b'{"error":"bad size"}', "application/json")
        audio = self.rfile.read(length)
        try:
            text = transcribe(audio, self.headers.get("Content-Type", "audio/webm"))
        except Exception:
            log.exception("transcribe failed")
            return self._send(502, b'{"error":"stt failed"}', "application/json")
        self._send(200, json.dumps({"text": text}, ensure_ascii=False).encode(), "application/json")

    def log_message(self, *args):
        pass


def start_web() -> None:
    if not (BASE / "index.html").exists():
        log.warning("index.html не найден, мини-приложение отдаваться не будет")
        return
    port = int(os.environ.get("PORT", "3000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), _PageHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    log.info("Мини-приложение доступно на порту %d", port)


async def post_init(app: Application) -> None:
    """Кнопка мини-приложения рядом с полем ввода (меню бота)."""
    try:
        await app.bot.set_chat_menu_button(menu_button=MenuButtonWebApp(
            text="🎙 Проверить", web_app=WebAppInfo(url=MINIAPP_URL)))
    except TelegramError:
        log.exception("Не удалось задать кнопку меню")


def main() -> None:
    token = os.environ.get("BOT_TOKEN")
    if not token:
        raise SystemExit("Задайте переменную окружения BOT_TOKEN (токен от @BotFather)")
    global TOKEN
    TOKEN = token
    global FONTS
    FONTS = ensure_fonts()
    load_data()
    load_subs()
    load_regions()
    start_web()

    app = Application.builder().token(token).post_init(post_init).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("menu", cmd_start))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("dua", cmd_dua))
    app.add_handler(CommandHandler("region", cmd_region))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_error_handler(on_error)
    app.job_queue.run_repeating(broadcast, interval=BROADCAST_SECONDS, first=BROADCAST_SECONDS)
    app.job_queue.run_repeating(prayer_tick, interval=30, first=15)
    log.info("Бот запущен")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
