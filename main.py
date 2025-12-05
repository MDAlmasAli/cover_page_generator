from email.mime import application
import os
from dotenv import load_dotenv
load_dotenv()
from telegram.request import HTTPXRequest
import logging
import json
import socket
import ssl
import csv
import glob
import math
import io
import asyncio
import httplib2
import zipfile
import shutil
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from pytz import timezone
from dateutil import parser
from telegram_bot_calendar import DetailedTelegramCalendar, LSTEP
from PyPDF2 import PdfReader, PdfWriter
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, ReplyKeyboardRemove
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    filters,
    ConversationHandler,
    CallbackContext,
    CallbackQueryHandler
)
from googleapiclient.discovery import build
from google.oauth2 import service_account
from googleapiclient.http import MediaIoBaseDownload
from googleapiclient.errors import HttpError
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from telegram.error import NetworkError, BadRequest

# Initialize Scheduler
scheduler = AsyncIOScheduler(timezone=timezone("Asia/Dhaka"))

# ===== Configuration =====
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# Google API setup
SCOPES = [
    'https://www.googleapis.com/auth/documents',
    'https://www.googleapis.com/auth/drive',
    'https://www.googleapis.com/auth/drive.file'
]

# Environment Variables
SERVICE_ACCOUNT_FILE = os.getenv("GOOGLE_SERVICE_ACCOUNT_FILE")
ASSIGNMENT_TEMPLATE_ID = os.getenv("ASSIGNMENT_TEMPLATE_ID")
LAB_TEMPLATE_ID = os.getenv("LAB_TEMPLATE_ID")
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
ADMIN_CHAT_IDS = os.getenv("ADMIN_CHAT_IDS", "").split(",")
ADMIN_CHAT_IDS = [chat_id.strip() for chat_id in ADMIN_CHAT_IDS if chat_id.strip()]

if not all([SERVICE_ACCOUNT_FILE, ASSIGNMENT_TEMPLATE_ID, LAB_TEMPLATE_ID, TELEGRAM_BOT_TOKEN]):
    raise ValueError("Missing essential environment variables!")

# --- PATH FIX START (এই অংশটুকু পরিবর্তন করা হয়েছে) ---
# বর্তমান স্ক্রিপ্টটি যে ফোল্ডারে আছে, তার লোকেশন বের করা
script_dir = os.path.dirname(os.path.abspath(__file__))

# ফাইলের সম্পূর্ণ পাথ (Absolute Path) তৈরি করা
USER_DATA_FILE = os.path.join(script_dir, "user_data.json")
VISITOR_LOG_FILE = os.path.join(script_dir, "visitor_log.json")
COVER_PAGE_LOG_FILE = os.path.join(script_dir, "cover_page_log.json")
ERROR_LOG_FILE = os.path.join(script_dir, "error_log.json")
CR_LIST_FILE = os.path.join(script_dir, "cr_list.json")
# --- PATH FIX END ---

COVER_PDF_GLOB = "cover_page_*.pdf"

# Field Mapping
FIELD_NAME_MAPPING = {
    'department': 'Department',
    'coursetitle': 'Course Title',
    'coursecode': 'Course Code',
    'assignmentno': 'Assignment No.',
    'assignmenttitle': 'Assignment Title',
    'experimentno': 'Experiment No.',
    'experimenttitle': 'Experiment Title',
    's_name': 'Student Name',
    's_id': 'Student ID',
    's_batch': 'Batch',
    's_section': 'Section',
    't_name': 'Teacher Name',
    't_designation': 'Teacher Designation',
    't_department': 'Teacher Department',
    'date': 'Date of Submission'
}

# ===== Department Constants =====
DEPT_OPTIONS = {
    "dept_cse": "Department of CSE",
    "dept_bba": "Department of BBA",
    "dept_eng": "Department of English",
    "dept_eee": "Department of EEE",
    "dept_civil": "Department of Civil Engineering",
    "dept_arch": "Department of Architecture",
    "dept_law": "Department of Law",
    "dept_islamic": "Department of Islamic Studies",
    "dept_ph": "Department of Public Health",
    "dept_thm": "Department of THM",
    "dept_bangla": "Department of Bangla"
}

# --- ১. ডেজিগনেশন অপশনগুলো ডিফাইন করুন (কোডের শুরুর দিকে) ---
DESIGNATION_OPTIONS = [
    "Adjunct Lecturer",
    "Lecturer",
    "Senior Lecturer",
    "Assistant Professor",
    "Associate Professor",
    "Professor",
    "Head of Department",
    "Guest Faculty"
]

# ===== Conversation States =====
(
    MENU_SELECTION,                 # 0
    ADD_COURSE_TITLE,               # 1
    ADD_COURSE_CODE,                # 2
    REMOVE_COURSE_SELECT,           # 3
    ADD_TEACHER_NAME,               # 4
    ADD_TEACHER_DESIG,              # 5
    ADD_TEACHER_DEPT,               # 6
    REMOVE_TEACHER_SELECT,          # 7
    COVER_PAGE_TYPE,                # 8
    STUDENT_DEPARTMENT,             # 9
    OTHER_DEPARTMENT,               # 10
    SELECT_SAVED_COURSE,            # 11
    COURSE_TITLE,                   # 12
    COURSE_CODE,                    # 13
    EXPERIMENT_OR_ASSIGNMENT_NO,    # 14
    EXPERIMENT_OR_ASSIGNMENT_TITLE, # 15
    S_NAME,                         # 16
    S_ID,                           # 17
    S_BATCH,                        # 18
    S_SECTION,                      # 19
    SELECT_SAVED_TEACHER,           # 20
    T_NAME,                         # 21
    T_DESIGNATION,                  # 22
    T_DEPARTMENT,                   # 23
    DATE,                           # 24
    CONFIRMATION,                   # 25
    EDIT_FIELD,                     # 26
    EDIT_SINGLE_FIELD,              # 27
    # --- Admin States ---
    ADMIN_HOME,                     # 28
    ADMIN_BROADCAST_WAIT,           # 29
    # --- Profile & Friend States ---
    MY_PROFILE_ACTION,              # 30
    FRIEND_PROFILE_ACTION,          # 31
    ADD_FRIEND_NAME,                # 32
    ADD_FRIEND_ID,                  # 33
    ADD_FRIEND_BATCH,               # 34
    ADD_FRIEND_SECTION,             # 35
    ADD_FRIEND_DEPT,                # 36
    SELECT_FRIEND_FOR_PDF,          # 37
    REMOVE_FRIEND_SELECT,           # 38
    # --- New Feedback State ---
    FEEDBACK_INPUT,                  # 39
    # --- Batch Mode States (Add these at the end) ---
    BATCH_SELECT,                   # 40
    SECTION_SELECT,                 # 41
    ADD_CR_ONLY_ID,                 # 42
    ADD_TEACHER_DESIG_MANUAL,       # 43
    T_DESIGNATION_MANUAL,           # 44
    ADD_TEACHER_DEPT_MANUAL,        # 45
    T_DEPARTMENT_MANUAL             # 46
) = range(47)

# Main Menu Keyboard
MAIN_MENU_KEYBOARD = ReplyKeyboardMarkup(
    [
        ["📄 Generate PDF", "👯 PDF for Friend"],
        ["📦 Sectionwise PDF"],
        ["👤 My Profile", "👥 Friend Profiles"],
        ["📚 Add Course", "🗑 Remove Course"],
        ["👨‍🏫 Add Teacher", "🗑 Remove Teacher"],
        ["💬 Feedback / Report Bug"]
    ],
    resize_keyboard=True,
    one_time_keyboard=False
)

# Admin Menu Keyboard
ADMIN_MENU_KEYS = [
    ["📢 Broadcast", "📊 Admin Report"],
    ["➕ Add CR", "🧑‍💬 Help User"],  # <--- এই লাইনটি চেঞ্জ হয়েছে
    ["❌ Close Menu"]
]
# Global services
docs_service = None
drive_service = None

# ===== Helper Functions =====

def get_desig_keyboard():
    keyboard = []
    # দুই কলামে বাটনগুলো সাজানো হবে
    row = []
    for desig in DESIGNATION_OPTIONS:
        row.append(InlineKeyboardButton(desig, callback_data=f"desig_{desig}"))
        if len(row) == 2:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
    
    # ম্যানুয়াল অপশন
    keyboard.append([InlineKeyboardButton("✍️ Manual Input", callback_data="desig_manual")])
    return InlineKeyboardMarkup(keyboard)
# ===== CR Management Helpers =====

def load_cr_list() -> list:
    """Load authorized CR IDs."""
    if not os.path.exists(CR_LIST_FILE):
        return []
    try:
        with open(CR_LIST_FILE, "r") as f:
            return json.load(f)
    except:
        return []

def save_cr_list(cr_ids: list):
    """Save CR list to file."""
    with open(CR_LIST_FILE, "w") as f:
        json.dump(cr_ids, f)

def is_user_cr(user_id: int) -> bool:
    """Check if user is a CR."""
    # এডমিনরা অটোমেটিক CR এর এক্সেস পাবে
    if str(user_id) in ADMIN_CHAT_IDS:
        return True
    
    cr_list = load_cr_list()
    return str(user_id) in cr_list

async def add_cr_command(update: Update, context: CallbackContext):
    """Admin command to add a new CR."""
    user_id = str(update.effective_user.id)
    
    # সিকিউরিটি চেক: শুধুমাত্র এডমিনরাই CR যোগ করতে পারবে
    if user_id not in ADMIN_CHAT_IDS:
        await update.message.reply_text("⛔ Unauthorized Access.")
        return

    try:
        new_cr_id = context.args[0].strip()
        cr_list = load_cr_list()
        
        if new_cr_id not in cr_list:
            cr_list.append(new_cr_id)
            save_cr_list(cr_list)
            await update.message.reply_text(f"✅ User `{new_cr_id}` promoted to **CR** successfully!", parse_mode="Markdown")
        else:
            await update.message.reply_text("⚠️ This user is already a CR.")
            
    except IndexError:
        await update.message.reply_text("⚠️ Usage: `/add_cr <Telegram_ID>`", parse_mode="Markdown")
def check_internet(timeout=3) -> bool:
    """Check internet connectivity."""
    servers = [("www.google.com", 443), ("www.cloudflare.com", 443)]
    for server, port in servers:
        try:
            socket.create_connection((server, port), timeout=timeout)
            return True
        except Exception as e:
            logging.error(f"Internet check failed for {server}:{port} - {e}")
    return False

def load_user_data(user_id: int) -> dict:
    """Load user data from JSON file."""
    try:
        if os.path.exists(USER_DATA_FILE):
            with open(USER_DATA_FILE, "r") as f:
                all_data = json.load(f)
                return all_data.get(str(user_id), {})
        return {}
    except json.JSONDecodeError:
        return {}

def save_user_data(user_id: int, data: dict) -> None:
    """Save persistent user data (Student Info)."""
    # NOTE: We only save if it's NOT a friend session
    if data.get('is_friend_session') is True:
        return

    try:
        if os.path.exists(USER_DATA_FILE):
            with open(USER_DATA_FILE, "r") as f:
                all_data = json.load(f)
        else:
            all_data = {}
    except json.JSONDecodeError:
        all_data = {}

    uid_str = str(user_id)
    if uid_str not in all_data:
        all_data[uid_str] = {}

    # Update student info fields
    student_fields = ["department", "s_name", "s_id", "s_batch", "s_section"]
    for field in student_fields:
        if field in data:
            all_data[uid_str][field] = data[field]

    try:
        with open(USER_DATA_FILE, "w") as f:
            json.dump(all_data, f, indent=4)
    except Exception as e:
        logger.error(f"Error saving user data: {e}")

def update_user_list(user_id: int, list_key: str, item, action: str = "add"):
    """Update lists like 'courses', 'teachers', or 'friends' in user_data.json."""
    try:
        if os.path.exists(USER_DATA_FILE):
            with open(USER_DATA_FILE, "r") as f:
                all_data = json.load(f)
        else:
            all_data = {}
    except json.JSONDecodeError:
        all_data = {}

    uid_str = str(user_id)
    if uid_str not in all_data:
        all_data[uid_str] = {}

    if list_key not in all_data[uid_str]:
        all_data[uid_str][list_key] = []

    if action == "add":
        # Avoid duplicates based on unique identifiers if possible, or simple check
        # For friends, maybe check name+id combination? For now, exact dict match check
        if item not in all_data[uid_str][list_key]:
            all_data[uid_str][list_key].append(item)
    elif action == "remove":
        try:
            # item is expected to be an index for removal
            idx = int(item)
            if 0 <= idx < len(all_data[uid_str][list_key]):
                all_data[uid_str][list_key].pop(idx)
        except Exception as e:
            logger.error(f"Error removing item: {e}")

    try:
        with open(USER_DATA_FILE, "w") as f:
            json.dump(all_data, f, indent=4)
    except Exception as e:
        logger.error(f"Error saving list data: {e}")

def get_user_list(user_id: int, list_key: str):
    """Retrieve a list (courses/teachers/friends) for a user."""
    data = load_user_data(user_id)
    return data.get(list_key, [])

# --- Logging Helpers ---
def log_visitor(user_id: int, username: str = None):
    try:
        logs = []
        if os.path.exists(VISITOR_LOG_FILE):
            with open(VISITOR_LOG_FILE, "r") as f:
                logs = json.load(f)
        logs.append({
            "user_id": user_id,
            "username": username or "Unknown",
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        with open(VISITOR_LOG_FILE, "w") as f:
            json.dump(logs, f, indent=4)
    except Exception as e:
        logger.error(f"Error logging visitor: {e}")

def log_cover_page(user_id: int, username: str):
    try:
        logs = []
        if os.path.exists(COVER_PAGE_LOG_FILE):
            with open(COVER_PAGE_LOG_FILE, "r") as f:
                logs = json.load(f)
        logs.append({
            "user_id": user_id,
            "username": username or "Unknown",
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        with open(COVER_PAGE_LOG_FILE, "w") as f:
            json.dump(logs, f, indent=4)
    except Exception as e:
        logger.error(f"Error logging cover page: {e}")

def log_error(user_id: int, error_message: str):
    try:
        logs = []
        if os.path.exists(ERROR_LOG_FILE):
            with open(ERROR_LOG_FILE, "r") as f:
                logs = json.load(f)
        logs.append({
            "user_id": user_id,
            "error_message": error_message,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        with open(ERROR_LOG_FILE, "w") as f:
            json.dump(logs, f, indent=4)
    except Exception as e:
        logger.error(f"Error logging error: {e}")

def get_dept_keyboard():
    """Helper to generate department buttons"""
    keyboard = []
    for key, value in DEPT_OPTIONS.items():
        keyboard.append([InlineKeyboardButton(value, callback_data=key)])

    keyboard.append([InlineKeyboardButton("✍️ Others (Manual Input)", callback_data="dept_other")])
    keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel")])
    return InlineKeyboardMarkup(keyboard)

# ===== Bot Handlers: Start & Menu =====

async def start(update: Update, context: CallbackContext) -> int:
    """Entry point: Show Main Menu."""
    user_id = update.effective_user.id
    username = update.effective_user.username
    log_visitor(user_id, username)

    # Clear session data
    context.user_data.clear()

    await update.message.reply_text(
        "👋 Welcome! What would you like to do?",
        reply_markup=MAIN_MENU_KEYBOARD
    )
    return MENU_SELECTION

async def menu_handler(update: Update, context: CallbackContext) -> int:
    """Handle Main Menu selections."""
    choice = update.message.text
    user_id = update.effective_user.id

    # --- PDF Generation Options ---
    if choice == "📄 Generate PDF":
        context.user_data['is_friend_session'] = False
        context.user_data['is_batch_mode'] = False
        return await start_generation_flow(update, context)

    elif choice == "👯 PDF for Friend":
        context.user_data['is_friend_session'] = True
        context.user_data['is_batch_mode'] = False
        return await start_friend_generation_flow(update, context)

    # --- NEW: Sectionwise PDF (Only for CRs) ---
    elif choice == "📦 Sectionwise PDF":
        # ১. চেক করা হচ্ছে ইউজার CR কিনা
        if not is_user_cr(user_id):
            warning_text = (
                "⛔ **Access Denied**\n\n"
                "This feature is reserved for **Class Representatives (CR)** only.\n\n"
                "To get access, please contact Admin with your details:\n"
                "👉 **t.me/verifylucsehelpline**\n\n"
                f"Your Telegram ID: `{user_id}`"
            )
            await update.message.reply_text(warning_text, parse_mode="Markdown")
            return MENU_SELECTION

        # ২. CR হলে এক্সেস দেওয়া হবে
        context.user_data['is_friend_session'] = False
        context.user_data['is_batch_mode'] = True
        return await start_batch_pdf_flow(update, context)

    # --- Profile Management ---
    elif choice == "👤 My Profile":
        return await show_my_profile(update, context)

    elif choice == "👥 Friend Profiles":
        return await show_friend_menu(update, context)

    # --- Course & Teacher Management ---
    elif choice == "📚 Add Course":
        await update.message.reply_text(
            "Enter the **Course Title** (e.g., Data Structures):",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardRemove()
        )
        return ADD_COURSE_TITLE

    elif choice == "🗑 Remove Course":
        return await show_remove_list(update, context, "courses", REMOVE_COURSE_SELECT)

    elif choice == "👨‍🏫 Add Teacher":
        await update.message.reply_text(
            "Enter the **Teacher's Name** (e.g., Mabrur Rashid):",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardRemove()
        )
        return ADD_TEACHER_NAME

    elif choice == "🗑 Remove Teacher":
        return await show_remove_list(update, context, "teachers", REMOVE_TEACHER_SELECT)

    # --- Feedback Trigger ---
    elif choice == "💬 Feedback / Report Bug":
        return await initiate_feedback(update, context)

    else:
        await update.message.reply_text(
            "❌ Please select an option from the menu.",
            reply_markup=MAIN_MENU_KEYBOARD
        )
        return MENU_SELECTION

# ===== Feedback Logic =====

async def initiate_feedback(update: Update, context: CallbackContext) -> int:
    """Asks user for feedback input."""
    await update.message.reply_text(
        "📝 **Feedback & Support**\n\n"
        "Facing any issues or have suggestions? Please write them below.\n"
        "We will try to resolve it as soon as possible.\n\n"
        "(To cancel, click any button from the main menu)",
        parse_mode="Markdown",
        reply_markup=ReplyKeyboardRemove() # Hides keyboard for easier typing
    )
    return FEEDBACK_INPUT

async def handle_feedback_message(update: Update, context: CallbackContext) -> int:
    """Sends the feedback to admins."""
    user = update.effective_user
    message = update.message.text

    # Format for Admin
    admin_text = (
        f"💬 **New Feedback Received**\n"
        f"👤 User: {user.full_name} (@{user.username})\n"
        f"🆔 ID: `{user.id}`\n"
        f"📅 Time: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n"
        f"📩 **Message:**\n{message}"
    )

    # Send to all admins
    for admin_id in ADMIN_CHAT_IDS:
        try:
            await context.bot.send_message(chat_id=admin_id, text=admin_text, parse_mode="Markdown")
        except Exception as e:
            logger.error(f"Failed to send feedback to admin {admin_id}: {e}")

    # Confirmation to User
    await update.message.reply_text(
        "✅ Your feedback has been received! Thank you.",
        reply_markup=MAIN_MENU_KEYBOARD
    )
    return MENU_SELECTION

# ===== My Profile Logic =====

async def show_my_profile(update: Update, context: CallbackContext) -> int:
    user_id = update.effective_user.id
    data = load_user_data(user_id)

    if 's_name' in data:
        info = (
            "👤 **My Saved Profile**\n\n"
            f"📛 Name: `{data.get('s_name', 'N/A')}`\n"
            f"🆔 ID: `{data.get('s_id', 'N/A')}`\n"
            f"🎓 Batch: `{data.get('s_batch', 'N/A')}`\n"
            f"🏫 Section: `{data.get('s_section', 'N/A')}`\n"
            f"🏛 Dept: `{data.get('department', 'N/A')}`"
        )
        keyboard = [
            [InlineKeyboardButton("🗑 Delete Profile", callback_data="delete_profile")],
            [InlineKeyboardButton("❌ Close", callback_data="cancel")]
        ]
    else:
        info = "👤 **My Profile**\n\nNo profile saved yet. Please generate a PDF first to save your data automatically."
        keyboard = [[InlineKeyboardButton("❌ Close", callback_data="cancel")]]

    await update.message.reply_text(info, parse_mode="Markdown", reply_markup=InlineKeyboardMarkup(keyboard))
    return MY_PROFILE_ACTION

async def my_profile_action(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "delete_profile":
        user_id = update.effective_user.id
        try:
            # We need to selectively remove fields but keep courses/teachers/friends
            if os.path.exists(USER_DATA_FILE):
                with open(USER_DATA_FILE, "r") as f:
                    all_data = json.load(f)

                uid = str(user_id)
                if uid in all_data:
                    # Remove student fields
                    for field in ["s_name", "s_id", "s_batch", "s_section", "department"]:
                        all_data[uid].pop(field, None)

                    with open(USER_DATA_FILE, "w") as f:
                        json.dump(all_data, f, indent=4)

            await query.edit_message_text("✅ Profile data deleted successfully.")
        except Exception as e:
            await query.edit_message_text("❌ Error deleting profile.")
            logger.error(f"Profile delete error: {e}")

    elif query.data == "cancel":
        await query.delete_message()
        await query.message.reply_text("Back to Main Menu", reply_markup=MAIN_MENU_KEYBOARD)

    return MENU_SELECTION

# ===== Friend Profile Logic =====

async def show_friend_menu(update: Update, context: CallbackContext) -> int:
    keyboard = [
        [InlineKeyboardButton("➕ Add New Friend", callback_data="add_friend")],
        [InlineKeyboardButton("📋 List/Remove Friends", callback_data="list_friends")],
        [InlineKeyboardButton("❌ Close", callback_data="cancel")]
    ]
    text = "👥 **Friend Profiles Management**"
    markup = InlineKeyboardMarkup(keyboard)

    # FIX: বাটন ক্লিক ও কমান্ড—উভয় ক্ষেত্রেই কাজ করবে
    if update.callback_query:
        # আগের মেসেজ এডিট করবে
        await update.callback_query.message.edit_text(text, parse_mode="Markdown", reply_markup=markup)
    else:
        # নতুন মেসেজ পাঠাবে
        await update.message.reply_text(text, parse_mode="Markdown", reply_markup=markup)

    return FRIEND_PROFILE_ACTION

async def friend_profile_action(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "cancel":
        await query.delete_message()
        await query.message.reply_text("Back to Main Menu", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    if query.data == "add_friend":
        await query.edit_message_text("Enter **Friend's Name**:", parse_mode="Markdown")
        return ADD_FRIEND_NAME

    if query.data == "list_friends":
        return await show_remove_list(update, context, "friends", REMOVE_FRIEND_SELECT)

    return FRIEND_PROFILE_ACTION

async def add_friend_name(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_f_name'] = update.message.text.strip()
    await update.message.reply_text("Enter **Friend's ID** (16 digits):", parse_mode="Markdown")
    return ADD_FRIEND_ID

async def add_friend_id(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_f_id'] = update.message.text.strip()
    await update.message.reply_text("Enter **Batch** (e.g. 62):", parse_mode="Markdown")
    return ADD_FRIEND_BATCH

async def add_friend_batch(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_f_batch'] = update.message.text.strip()
    await update.message.reply_text("Enter **Section** (e.g. A):", parse_mode="Markdown")
    return ADD_FRIEND_SECTION

async def add_friend_section(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_f_section'] = update.message.text.strip()

    # Show New Department List for Friend
    await update.message.reply_text(
        "Select **Friend's Department**:",
        parse_mode="Markdown",
        reply_markup=get_dept_keyboard()
    )
    return ADD_FRIEND_DEPT

async def add_friend_dept(update: Update, context: CallbackContext) -> int:
    dept = None

    # Handle Button Click
    if update.callback_query:
        await update.callback_query.answer()
        data = update.callback_query.data

        if data == 'cancel':
            return await cancel(update, context)

        if data in DEPT_OPTIONS:
            dept = DEPT_OPTIONS[data]
        elif data == 'dept_other':
            await update.callback_query.edit_message_text("Enter Department Name manually:")
            return ADD_FRIEND_DEPT # Wait for text input next

    # Handle Manual Text Input
    elif update.message:
        dept = update.message.text.strip()

    # If we got a department, save the friend
    if dept:
        user_id = update.effective_user.id

        friend_data = {
            "title": context.user_data['temp_f_name'],
            "s_name": context.user_data['temp_f_name'],
            "s_id": context.user_data['temp_f_id'],
            "s_batch": context.user_data['temp_f_batch'],
            "s_section": context.user_data['temp_f_section'],
            "department": dept
        }

        update_user_list(user_id, "friends", friend_data, action="add")

        msg_text = f"✅ Friend **{friend_data['s_name']}** saved with Dept: {dept}!"

        if update.callback_query:
            await update.callback_query.edit_message_text(msg_text, parse_mode="Markdown")
            await asyncio.sleep(1)
            await context.bot.send_message(chat_id=user_id, text="Main Menu:", reply_markup=MAIN_MENU_KEYBOARD)
        else:
            await update.message.reply_text(msg_text, parse_mode="Markdown", reply_markup=MAIN_MENU_KEYBOARD)

        return MENU_SELECTION

    return ADD_FRIEND_DEPT

async def remove_friend_handler(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "cancel":
        return await show_friend_menu(update, context)

    idx = int(query.data.split("_")[1])
    update_user_list(update.effective_user.id, "friends", idx, action="remove")
    await query.edit_message_text("✅ Friend removed.")

    await asyncio.sleep(1)
    return await show_friend_menu(update, context)

# ===== Friend PDF Generation Flow =====

async def start_friend_generation_flow(update: Update, context: CallbackContext) -> int:
    """Select a friend to generate PDF for."""
    user_id = update.effective_user.id
    friends = get_user_list(user_id, "friends")

    if not friends:
        await update.message.reply_text(
            "❌ No friends saved! Go to **Friend Profiles** to add one first.",
            parse_mode="Markdown",
            reply_markup=MAIN_MENU_KEYBOARD
        )
        return MENU_SELECTION

    keyboard = []
    for idx, f in enumerate(friends):
        keyboard.append([InlineKeyboardButton(f"👤 {f['s_name']} ({f['s_id']})", callback_data=f"frpdf_{idx}")])

    keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel")])

    await update.message.reply_text(
        "👯 Select a friend to generate PDF for:",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return SELECT_FRIEND_FOR_PDF

async def select_friend_for_pdf(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "cancel":
        await query.delete_message()
        await query.message.reply_text("Cancelled", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    idx = int(query.data.split("_")[1])
    friends = get_user_list(update.effective_user.id, "friends")

    if idx < len(friends):
        f = friends[idx]
        context.user_data.update({
            "s_name": f['s_name'],
            "s_id": f['s_id'],
            "s_batch": f['s_batch'],
            "s_section": f['s_section'],
            "department": f.get('department', ''), # <--- ডিপার্টমেন্ট লোড হচ্ছে
            "is_friend_session": True
        })

        await query.edit_message_text(f"✅ Selected Friend: **{f['s_name']}**", parse_mode="Markdown")

        keyboard = [
            [InlineKeyboardButton("Assignment", callback_data='assignment')],
            [InlineKeyboardButton("Lab", callback_data='lab')],
            [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
        ]
        await query.message.reply_text("Type?", reply_markup=InlineKeyboardMarkup(keyboard))
        return COVER_PAGE_TYPE

    return MENU_SELECTION

# ===== Add / Remove Logic (Courses/Teachers) =====

async def add_course_title(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_course_title'] = update.message.text.strip()
    await update.message.reply_text("Enter the **Course Code** (e.g., CSE-2202):", parse_mode="Markdown")
    return ADD_COURSE_CODE

async def add_course_code(update: Update, context: CallbackContext) -> int:
    code = update.message.text.strip()
    title = context.user_data.get('temp_course_title')
    user_id = update.effective_user.id

    new_course = {"title": title, "code": code}
    update_user_list(user_id, "courses", new_course, action="add")

    await update.message.reply_text(
        f"✅ Saved Course:\n**{title}** ({code})",
        parse_mode="Markdown",
        reply_markup=MAIN_MENU_KEYBOARD
    )
    return MENU_SELECTION

async def add_teacher_name(update: Update, context: CallbackContext) -> int:
    # নাম সেভ করা
    context.user_data['temp_t_name'] = update.message.text.strip()
    
    # বাটন দেখানো
    await update.message.reply_text(
        "Select **Designation**:",
        parse_mode="Markdown",
        reply_markup=get_desig_keyboard()
    )
    return ADD_TEACHER_DESIG

# --- ১. ডেজিগনেশন সিলেক্ট করার পর ---
async def add_teacher_desig(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    
    data = query.data
    
    if data == "desig_manual":
        await query.edit_message_text("Enter Designation manually:")
        return ADD_TEACHER_DESIG_MANUAL

    elif data.startswith("desig_"):
        desig = data.split("_", 1)[1]
        context.user_data['temp_t_desig'] = desig
        
        await query.edit_message_text(f"✅ Selected: **{desig}**", parse_mode="Markdown")
        
        # [CHANGE] এখন বাটন দেখাবে
        await query.message.reply_text(
            "Select **Department**:",
            parse_mode="Markdown",
            reply_markup=get_dept_keyboard() # আপনার কোডে এই ফাংশন অলরেডি আছে
        )
        return ADD_TEACHER_DEPT

# --- ২. ম্যানুয়াল ডেজিগনেশন দেওয়ার পর ---
async def add_teacher_desig_manual(update: Update, context: CallbackContext) -> int:
    context.user_data['temp_t_desig'] = update.message.text.strip()
    
    # [CHANGE] এখানেও বাটন দেখাবে
    await update.message.reply_text(
        "Select **Department**:",
        parse_mode="Markdown",
        reply_markup=get_dept_keyboard()
    )
    return ADD_TEACHER_DEPT

# --- ৩. বাটন হ্যান্ডেল করা ---
async def add_teacher_dept(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    
    data = query.data

    # ম্যানুয়াল অপশন সিলেক্ট করলে
    if data == 'dept_other':
        await query.edit_message_text("Enter Department Name manually:")
        return ADD_TEACHER_DEPT_MANUAL

    elif data == 'cancel':
        return await cancel(update, context)

    # লিস্ট থেকে সিলেক্ট করলে
    elif data in DEPT_OPTIONS:
        dept_name = DEPT_OPTIONS[data] # ভ্যালু বের করা (যেমন: Dept of CSE)
        
        # ডাটা সেভ করা
        user_id = update.effective_user.id
        new_teacher = {
            "name": context.user_data.get('temp_t_name'),
            "designation": context.user_data.get('temp_t_desig'),
            "department": dept_name,
            "title": context.user_data.get('temp_t_name')
        }
        update_user_list(user_id, "teachers", new_teacher, action="add")

        await query.edit_message_text(
            f"✅ Teacher Saved!\n👨‍🏫 **{new_teacher['name']}**\n🎓 {new_teacher['designation']}\n🏫 {dept_name}",
            parse_mode="Markdown"
        )
        # মেইন মেনুতে ফেরত
        await asyncio.sleep(1)
        await query.message.reply_text("Main Menu:", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

# --- ৪. ম্যানুয়াল ইনপুট হ্যান্ডেল করা ---
async def add_teacher_dept_manual(update: Update, context: CallbackContext) -> int:
    dept_name = update.message.text.strip()
    
    # ডাটা সেভ করা
    user_id = update.effective_user.id
    new_teacher = {
        "name": context.user_data.get('temp_t_name'),
        "designation": context.user_data.get('temp_t_desig'),
        "department": dept_name,
        "title": context.user_data.get('temp_t_name')
    }
    update_user_list(user_id, "teachers", new_teacher, action="add")

    await update.message.reply_text(
        f"✅ Teacher Saved!\n👨‍🏫 **{new_teacher['name']}**\n🎓 {new_teacher['designation']}\n🏫 {dept_name}",
        parse_mode="Markdown",
        reply_markup=MAIN_MENU_KEYBOARD
    )
    return MENU_SELECTION

async def show_remove_list(update: Update, context: CallbackContext, list_key: str, next_state: int):
    user_id = update.effective_user.id
    items = get_user_list(user_id, list_key)

    # FIX: মেসেজ অবজেক্ট ঠিকভাবে ধরা
    if update.callback_query:
        message = update.callback_query.message
    else:
        message = update.message

    if not items:
        warning_text = "❌ No saved items found."
        if update.callback_query:
            await message.edit_text(warning_text)
            await asyncio.sleep(1.5)
            if list_key == "friends":
                return await show_friend_menu(update, context)
            else:
                await message.reply_text("Main Menu:", reply_markup=MAIN_MENU_KEYBOARD)
                return MENU_SELECTION
        else:
            await message.reply_text(warning_text, reply_markup=MAIN_MENU_KEYBOARD)
            return MENU_SELECTION

    keyboard = []
    for idx, item in enumerate(items):
        # FIX: এখানে 'name' যোগ করা হয়েছে যাতে টিচারদের নাম ঠিকমতো দেখায়
        # Priority: title (Course/Friend) -> name (Teacher) -> s_name (Friend) -> Unknown
        label = item.get('title') or item.get('name') or item.get('s_name') or 'Unknown'

        keyboard.append([InlineKeyboardButton(f"🗑 {label}", callback_data=f"rm_{idx}")])

    keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel")])

    if update.callback_query:
        await message.edit_text(
            f"Select an item to remove:",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
    else:
        await message.reply_text(
            f"Select an item to remove:",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )

    return next_state

async def remove_course_handler(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    if query.data == "cancel":
        await query.delete_message()
        await query.message.reply_text("Cancelled.", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    idx = int(query.data.split("_")[1])
    update_user_list(update.effective_user.id, "courses", idx, action="remove")
    await query.edit_message_text("✅ Course removed.")

    await asyncio.sleep(1)
    await query.message.reply_text("Back to menu:", reply_markup=MAIN_MENU_KEYBOARD)
    return MENU_SELECTION

async def remove_teacher_handler(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    if query.data == "cancel":
        await query.delete_message()
        await query.message.reply_text("Cancelled.", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    idx = int(query.data.split("_")[1])
    update_user_list(update.effective_user.id, "teachers", idx, action="remove")
    await query.edit_message_text("✅ Teacher removed.")

    await asyncio.sleep(1)
    await query.message.reply_text("Back to menu:", reply_markup=MAIN_MENU_KEYBOARD)
    return MENU_SELECTION

# ===== PDF Generation Flow (Self) =====

async def start_generation_flow(update: Update, context: CallbackContext) -> int:
    """Initiate the cover page generation process (Self)."""
    user_id = update.effective_user.id
    previous_data = load_user_data(user_id)

    # Check if student info exists
    if previous_data and 's_name' in previous_data:
        context.user_data.update(previous_data) # Load student info
        context.user_data['is_friend_session'] = False

        info_summary = (
            "📋 **Found previous student info:**\n\n"
            f"👤 **Name:** {previous_data.get('s_name', 'N/A')}\n"
            f"🆔 **ID:** {previous_data.get('s_id', 'N/A')}\n"
            f"🎓 **Batch:** {previous_data.get('s_batch', 'N/A')}\n"
            f"🏫 **Section:** {previous_data.get('s_section', 'N/A')}\n"
            f"🏛 **Dept:** {previous_data.get('department', 'N/A')}\n\n"
            "Do you want to use this details?"
        )

        keyboard = [
            [InlineKeyboardButton("✅ Yes, Use This", callback_data='use_previous')],
            [InlineKeyboardButton("❌ No, Start Fresh", callback_data='start_fresh')],
        ]

        if update.callback_query:
            await update.callback_query.message.reply_text(info_summary, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
        else:
            await update.message.reply_text(info_summary, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

        return COVER_PAGE_TYPE

    # No data, start normal flow
    keyboard = [
        [InlineKeyboardButton("Assignment", callback_data='assignment')],
        [InlineKeyboardButton("Lab", callback_data='lab')],
        [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
    ]
    await update.message.reply_text(
        "Which cover page would you like to generate?",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return COVER_PAGE_TYPE

async def cover_page_type(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == 'cancel':
        return await cancel(update, context)

    # Logic to handle Start Fresh / Use Previous selection
    if query.data == 'start_fresh':
        context.user_data.clear()
        context.user_data['is_fresh_start'] = True
        context.user_data['is_friend_session'] = False

        # Show Type Selection again
        keyboard = [
            [InlineKeyboardButton("Assignment", callback_data='assignment')],
            [InlineKeyboardButton("Lab", callback_data='lab')],
            [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
        ]
        await query.edit_message_text(
            "Which cover page would you like to generate?",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
        return COVER_PAGE_TYPE

    elif query.data == 'use_previous':
        context.user_data['is_fresh_start'] = False
        # Show Type Selection
        keyboard = [
            [InlineKeyboardButton("Assignment", callback_data='assignment')],
            [InlineKeyboardButton("Lab", callback_data='lab')],
            [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
        ]
        await query.edit_message_text(
            "Which cover page would you like to generate?",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
        return COVER_PAGE_TYPE

    # Store Cover Type (Assignment/Lab)
    if query.data in ['assignment', 'lab']:
        context.user_data['cover_page_type'] = query.data
        await query.edit_message_text(text=f"Selected: {query.data.capitalize()}")

        # FIX: Skip department check if already exists and not fresh start
        if not context.user_data.get('is_fresh_start') and context.user_data.get('department'):
            return await check_saved_courses(update, context)

        # Show New Department List
        await query.message.reply_text("Select your Department:", reply_markup=get_dept_keyboard())
        return STUDENT_DEPARTMENT

    return COVER_PAGE_TYPE

# --- Course Selection Logic ---
async def check_saved_courses(update: Update, context: CallbackContext):
    """Checks if saved courses exist."""
    user_id = update.effective_user.id
    courses = get_user_list(user_id, "courses")

    if courses:
        keyboard = []
        for idx, c in enumerate(courses):
            keyboard.append([InlineKeyboardButton(f"{c['title']} ({c['code']})", callback_data=f"course_{idx}")])

        keyboard.append([InlineKeyboardButton("➕ Manual Entry", callback_data="course_new")])

        msg_text = "📚 Select a Course:"
        if update.callback_query:
            await update.callback_query.message.reply_text(msg_text, reply_markup=InlineKeyboardMarkup(keyboard))
        else:
            await update.message.reply_text(msg_text, reply_markup=InlineKeyboardMarkup(keyboard))
        return SELECT_SAVED_COURSE
    else:
        # No saved courses
        msg_text = "Enter Course Title: (Example: Data Structures)"
        if update.callback_query:
            await update.callback_query.message.reply_text(msg_text)
        else:
            await update.message.reply_text(msg_text)
        return COURSE_TITLE

async def student_department(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == 'cancel':
        return await cancel(update, context)

    # Check if a valid department button was clicked
    if query.data in DEPT_OPTIONS:
        dept_name = DEPT_OPTIONS[query.data]
        context.user_data['department'] = dept_name
        await query.edit_message_text(f"✅ Department: {dept_name}")
        return await check_saved_courses(update, context)

    elif query.data == 'dept_other':
        await query.edit_message_text("Enter your department name manually:")
        return OTHER_DEPARTMENT

    else:
        await query.edit_message_text("❌ Invalid selection.")
        return MENU_SELECTION

async def other_department(update: Update, context: CallbackContext) -> int:
    context.user_data["department"] = update.message.text.strip()
    return await check_saved_courses(update, context)

async def select_saved_course(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "course_new":
        await query.edit_message_text("Enter Course Title:")
        return COURSE_TITLE

    if query.data.startswith("course_"):
        idx = int(query.data.split("_")[1])
        courses = get_user_list(update.effective_user.id, "courses")
        if idx < len(courses):
            selected = courses[idx]
            context.user_data['coursetitle'] = selected['title']
            context.user_data['coursecode'] = selected['code']
            await query.edit_message_text(f"Selected: {selected['title']}")

            prompt = "Enter Experiment No.:" if context.user_data['cover_page_type'] == 'lab' else "Enter Assignment No.:"
            await query.message.reply_text(prompt)
            return EXPERIMENT_OR_ASSIGNMENT_NO
        else:
            await query.edit_message_text("Error loading course.")
            return await check_saved_courses(update, context)

async def course_title(update: Update, context: CallbackContext) -> int:
    context.user_data["coursetitle"] = update.message.text.strip()
    await update.message.reply_text("Enter Course Code: (Example: CSE-2202)")
    return COURSE_CODE

async def course_code(update: Update, context: CallbackContext) -> int:
    context.user_data["coursecode"] = update.message.text.strip()
    prompt = "Enter Experiment No.:" if context.user_data['cover_page_type'] == 'lab' else "Enter Assignment No.:"
    await update.message.reply_text(prompt)
    return EXPERIMENT_OR_ASSIGNMENT_NO

async def experiment_or_assignment_no(update: Update, context: CallbackContext) -> int:
    key = "experimentno" if context.user_data['cover_page_type'] == 'lab' else "assignmentno"
    context.user_data[key] = update.message.text.strip()

    prompt = "Enter Experiment Title:" if context.user_data['cover_page_type'] == 'lab' else "Enter Assignment Title:"
    await update.message.reply_text(prompt)
    return EXPERIMENT_OR_ASSIGNMENT_TITLE

async def experiment_or_assignment_title(update: Update, context: CallbackContext) -> int:
    key = "experimenttitle" if context.user_data['cover_page_type'] == 'lab' else "assignmenttitle"
    context.user_data[key] = update.message.text.strip()

    # --- CHANGE START ---
    # যদি Batch Mode হয়, তবে স্টুডেন্ট ইনফো স্কিপ করে সরাসরি টিচার সিলেকশনে চলে যাব
    if context.user_data.get('is_batch_mode'):
        return await check_saved_teachers(update, context)
    # --- CHANGE END ---

    # Check if student info exists (Self or Friend Session)
    if (not context.user_data.get('is_fresh_start')) and context.user_data.get('s_name'):
        return await check_saved_teachers(update, context)

    await update.message.reply_text("Enter Student Name:")
    return S_NAME

async def s_name(update: Update, context: CallbackContext) -> int:
    context.user_data["s_name"] = update.message.text.strip()
    await update.message.reply_text("Enter Student ID: (16 digits)")
    return S_ID

async def s_id(update: Update, context: CallbackContext) -> int:
    user_input = update.message.text.strip()
    if not user_input.isdigit() or len(user_input) != 16:
        await update.message.reply_text("❌ Invalid ID! Must be 16 digits.")
        return S_ID
    context.user_data["s_id"] = user_input
    await update.message.reply_text("Enter Batch: (Example: 60)")
    return S_BATCH

async def s_batch(update: Update, context: CallbackContext) -> int:
    context.user_data["s_batch"] = update.message.text.strip()
    await update.message.reply_text("Enter Section: (Example: A)")
    return S_SECTION

async def s_section(update: Update, context: CallbackContext) -> int:
    context.user_data["s_section"] = update.message.text.strip()
    return await check_saved_teachers(update, context)

# --- Teacher Selection Logic ---
async def check_saved_teachers(update: Update, context: CallbackContext):
    """Checks if saved teachers exist."""
    user_id = update.effective_user.id
    teachers = get_user_list(user_id, "teachers")

    # Message might come from text update or callback or internal call
    reply_method = update.message.reply_text if update.message else context.bot.send_message

    if teachers:
        keyboard = []
        for idx, t in enumerate(teachers):
            keyboard.append([InlineKeyboardButton(f"{t['name']}", callback_data=f"teacher_{idx}")])
        keyboard.append([InlineKeyboardButton("➕ Manual Entry", callback_data="teacher_new")])

        await reply_method("👨‍🏫 Select a Teacher:", reply_markup=InlineKeyboardMarkup(keyboard))
        return SELECT_SAVED_TEACHER
    else:
        await reply_method("Enter Teacher Name:")
        return T_NAME

async def select_saved_teacher(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == "teacher_new":
        await query.edit_message_text("Enter Teacher Name:")
        return T_NAME

    if query.data.startswith("teacher_"):
        idx = int(query.data.split("_")[1])
        teachers = get_user_list(update.effective_user.id, "teachers")
        if idx < len(teachers):
            selected = teachers[idx]
            context.user_data['t_name'] = selected['name']
            context.user_data['t_designation'] = selected['designation']
            context.user_data['t_department'] = selected['department']

            await query.edit_message_text(f"Selected Teacher: {selected['name']}")

            # --- CALENDAR TRIGGER ---
            calendar, step = DetailedTelegramCalendar().build()
            await query.message.reply_text(f"📅 Select {LSTEP[step]}", reply_markup=calendar)
            return DATE
        else:
            await query.edit_message_text("Error loading teacher.")
            return await check_saved_teachers(update, context)

async def t_name(update: Update, context: CallbackContext) -> int:
    context.user_data["t_name"] = update.message.text.strip()
    
    await update.message.reply_text(
        "Select **Teacher's Designation**:",
        parse_mode="Markdown",
        reply_markup=get_desig_keyboard()
    )
    return T_DESIGNATION

# --- ১. ডেজিগনেশন সিলেক্ট (PDF Flow) ---
async def t_designation(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    
    data = query.data

    if data == "desig_manual":
        await query.edit_message_text("Enter Teacher Designation manually:")
        return T_DESIGNATION_MANUAL

    elif data.startswith("desig_"):
        desig = data.split("_", 1)[1]
        context.user_data["t_designation"] = desig
        
        await query.edit_message_text(f"✅ Designation: **{desig}**", parse_mode="Markdown")
        
        # [CHANGE] ডিপার্টমেন্ট বাটন শো করা
        await query.message.reply_text(
            "Select **Teacher's Department**:",
            parse_mode="Markdown",
            reply_markup=get_dept_keyboard()
        )
        return T_DEPARTMENT

# --- ২. ম্যানুয়াল ডেজিগনেশন (PDF Flow) ---
async def t_designation_manual(update: Update, context: CallbackContext) -> int:
    context.user_data["t_designation"] = update.message.text.strip()
    
    # [CHANGE] ডিপার্টমেন্ট বাটন শো করা
    await update.message.reply_text(
        "Select **Teacher's Department**:",
        parse_mode="Markdown",
        reply_markup=get_dept_keyboard()
    )
    return T_DEPARTMENT

# --- ৩. ডিপার্টমেন্ট বাটন হ্যান্ডেল করা ---
async def t_department(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()
    
    data = query.data

    if data == 'dept_other':
        await query.edit_message_text("Enter Department Name manually:")
        return T_DEPARTMENT_MANUAL

    elif data == 'cancel':
        return await cancel(update, context)

    elif data in DEPT_OPTIONS:
        context.user_data["t_department"] = DEPT_OPTIONS[data]
        await query.edit_message_text(f"✅ Dept: {DEPT_OPTIONS[data]}")

        # ক্যালেন্ডার ট্রিগার
        calendar, step = DetailedTelegramCalendar().build()
        await query.message.reply_text(f"📅 Select {LSTEP[step]}", reply_markup=calendar)
        return DATE

# --- ৪. ম্যানুয়াল ইনপুট হ্যান্ডেল করা ---
async def t_department_manual(update: Update, context: CallbackContext) -> int:
    context.user_data["t_department"] = update.message.text.strip()
    
    # ক্যালেন্ডার ট্রিগার
    calendar, step = DetailedTelegramCalendar().build()
    await update.message.reply_text(f"📅 Select {LSTEP[step]}", reply_markup=calendar)
    return DATE

async def handle_calendar_date(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    # ক্যালেন্ডারের ডাটা প্রসেস করা
    result, key, step = DetailedTelegramCalendar().process(query.data)

    if not result and key:
        # ইউজার এখনো তারিখ সিলেক্ট করেনি (সাল বা মাস চেঞ্জ করছে)
        await query.edit_message_text(f"📅 Select {LSTEP[step]}", reply_markup=key)
        return DATE

    elif result:
        # ইউজার তারিখ সিলেক্ট করেছে
        formatted_date = result.strftime("%d %B %Y") # Format: 15 April 2025
        context.user_data["date"] = formatted_date

        await query.edit_message_text(f"✅ Date Selected: {formatted_date}")

        # সরাসরি সামারি দেখাবে
        return await show_summary(update, context)

async def show_summary(update: Update, context: CallbackContext) -> int:
    data = context.user_data
    cover_type = data.get('cover_page_type', 'assignment')

    summary = (
        "📋 **Confirm Details:**\n\n"
        f"🔹 **Type:** {cover_type.capitalize()}\n"
        f"🔹 **Course:** {data.get('coursetitle', 'N/A')} ({data.get('coursecode', 'N/A')})\n"
        f"🔹 **No:** {data.get('experimentno', data.get('assignmentno', 'N/A'))}\n"
        f"🔹 **Title:** {data.get('experimenttitle', data.get('assignmenttitle', 'N/A'))}\n"
        f"🔹 **Student:** {data.get('s_name', 'N/A')} ({data.get('s_id', 'N/A')})\n"
        f"🔹 **Teacher:** {data.get('t_name', 'N/A')}\n"
        f"🔹 **Date:** {data.get('date', 'N/A')}\n"
    )

    keyboard = [
        [InlineKeyboardButton("✅ Confirm & Generate", callback_data='confirm')],
        [InlineKeyboardButton("✏ Edit Details", callback_data='edit')],
        [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
    ]

    if update.callback_query:
        await update.callback_query.edit_message_text(
            text=summary,
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text(
            text=summary,
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode="Markdown"
        )
    return CONFIRMATION

async def confirm_details(update: Update, context: CallbackContext) -> int:
    """Handle confirmation or edit."""
    query = update.callback_query
    await query.answer()

    if query.data == 'confirm':
        await query.edit_message_text(text="⏳ Generating your cover page...")
        return await generate_final_pdf(update, context)

    elif query.data == 'edit':
        cover_type = context.user_data.get('cover_page_type', 'assignment')

        common_fields = ['department', 'coursetitle', 'coursecode']
        student_fields = ['s_name', 's_id', 's_batch', 's_section']
        teacher_fields = ['t_name', 't_designation', 't_department']
        date_field = ['date']

        if cover_type == 'lab':
            specific_fields = ['experimentno', 'experimenttitle']
        else:
            specific_fields = ['assignmentno', 'assignmenttitle']

        all_relevant_fields = common_fields + specific_fields + student_fields + teacher_fields + date_field

        keyboard = []
        for f in all_relevant_fields:
            if f in FIELD_NAME_MAPPING:
                label = FIELD_NAME_MAPPING[f]
                keyboard.append([InlineKeyboardButton(f"✏️ Edit {label}", callback_data=f'edit_{f}')])

        keyboard.append([InlineKeyboardButton("🔙 Back", callback_data='back_to_summary')])
        keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data='cancel')])

        await query.edit_message_text(
            "Select the field you want to edit:",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
        return EDIT_FIELD

    elif query.data == 'back_to_summary':
        return await show_summary(update, context)

    elif query.data == 'cancel':
        return await cancel(update, context)

async def edit_field(update: Update, context: CallbackContext) -> int:
    query = update.callback_query
    await query.answer()

    if query.data == 'back_to_summary':
        return await show_summary(update, context)

    if query.data.startswith('edit_'):
        field = query.data[len('edit_'):]
        if field in FIELD_NAME_MAPPING:
            context.user_data['editing_field'] = field
            await query.edit_message_text(f"Enter new value for **{FIELD_NAME_MAPPING[field]}**:", parse_mode="Markdown")
            return EDIT_SINGLE_FIELD

    return await cancel(update, context)

async def edit_single_field(update: Update, context: CallbackContext) -> int:
    field = context.user_data.get('editing_field')
    context.user_data[field] = update.message.text.strip()
    del context.user_data['editing_field']
    return await show_summary(update, context)

async def generate_final_pdf(update: Update, context: CallbackContext) -> int:
    # --- 1. Check for Batch Mode ---
    # যদি ব্যাচ মোড অন থাকে, তাহলে আমরা সিঙ্গেল PDF ফ্লো স্কিপ করে ব্যাচ ফ্লোতে চলে যাব
    if context.user_data.get('is_batch_mode'):
        return await generate_batch_zip(update, context)

    # --- 2. Existing Single PDF Logic ---
    try:
        if not check_internet():
            await update.effective_chat.send_message("❌ No internet connection.")
            return MENU_SELECTION

        user_id = update.effective_user.id
        template_id = LAB_TEMPLATE_ID if context.user_data['cover_page_type'] == 'lab' else ASSIGNMENT_TEMPLATE_ID

        # Google Docs API Logic
        doc_copy = drive_service.files().copy(
            fileId=template_id,
            body={"name": f"Cover_Page_{user_id}"}
        ).execute()

        requests = []
        for key, value in context.user_data.items():
            # অপ্রয়োজনীয় কী (Keys) বাদ দেওয়া হচ্ছে
            if isinstance(value, str) and key not in ['cover_page_type', 'editing_field', 'is_fresh_start', 'is_friend_session', 'is_batch_mode', 'temp_f_name', 'temp_f_id', 'temp_f_batch']:
                requests.append({
                    'replaceAllText': {
                        'containsText': {'text': f"{{{key}}}", 'matchCase': False},
                        'replaceText': value
                    }
                })

        if requests:
            docs_service.documents().batchUpdate(
                documentId=doc_copy['id'], body={'requests': requests}
            ).execute()

        # Export PDF
        pdf_content = drive_service.files().export(
            fileId=doc_copy['id'], mimeType="application/pdf"
        ).execute()

        pdf_path = f"cover_page_{user_id}.pdf"
        with open(pdf_path, "wb") as f:
            f.write(pdf_content)

        # Send to user
        with open(pdf_path, "rb") as f:
            await update.effective_chat.send_document(document=f, caption="✅ Cover page generated!")

        # 🔔 Send to Admins
        admin_caption = (
            f"🔔 **New Cover Page Generated**\n"
            f"👤 User: {update.effective_user.full_name} (@{update.effective_user.username})\n"
            f"🆔 ID: `{user_id}`\n"
            f"👥 Friend Session: `{context.user_data.get('is_friend_session', False)}`\n"
            f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
        )

        for admin_id in ADMIN_CHAT_IDS:
            try:
                with open(pdf_path, "rb") as f:
                    await context.bot.send_document(
                        chat_id=admin_id,
                        document=f,
                        caption=admin_caption,
                        parse_mode="Markdown"
                    )
            except Exception as e:
                logger.error(f"Failed to send PDF to admin {admin_id}: {e}")

        # Log & Cleanup
        log_cover_page(user_id, update.effective_user.username)
        
        # IMPORTANT: Only save data if it's NOT a friend session AND NOT batch mode
        if not context.user_data.get('is_friend_session'):
            save_user_data(user_id, context.user_data)

        try:
            os.remove(pdf_path)
            drive_service.files().delete(fileId=doc_copy['id']).execute()
        except Exception:
            pass

        # Back to Menu
        await update.effective_chat.send_message("What would you like to do next?", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    except Exception as e:
        logger.exception(f"PDF Gen Error: {e}")
        await update.effective_chat.send_message("❌ Error generating PDF. Try again later.")
        log_error(update.effective_user.id, str(e))
        return MENU_SELECTION

async def generate_batch_zip(update: Update, context: CallbackContext) -> int:
    status_msg = await update.callback_query.message.reply_text("⏳ **Initializing Batch Process...**\nFetching student data...", parse_mode="Markdown")
    
    try:
        batch = context.user_data['target_batch']
        sec = context.user_data['target_section']
        template_id = LAB_TEMPLATE_ID if context.user_data['cover_page_type'] == 'lab' else ASSIGNMENT_TEMPLATE_ID
        
        # ১. স্টুডেন্ট ফিল্টার করা (UID সহ)
        with open(USER_DATA_FILE, "r") as f:
            all_data = json.load(f)
            
        students = []
        # আমরা UID-ও রাখব যাতে তাদের মেসেজ পাঠানো যায়
        for uid, data in all_data.items():
            if data.get('s_batch') == batch and data.get('s_section') == sec:
                students.append({"uid": uid, "data": data})
                
        if not students:
            await status_msg.edit_text("❌ No students found for this batch/section.")
            return MENU_SELECTION

        total = len(students)
        await status_msg.edit_text(f"🚀 **Starting Task...**\nfound {total} students.")

        # ২. টেম্পোরারি ফোল্ডার তৈরি
        temp_dir = f"Batch_{batch}_{sec}_{datetime.now().strftime('%H%M%S')}"
        os.makedirs(temp_dir, exist_ok=True)

        # ৩. লুপ চালানো (Batch Processing)
        generated_count = 0
        success_log = "" # এখানে আমরা নামগুলো জমা করব
        
        for i, item in enumerate(students):
            uid = item['uid']
            std = item['data']
            s_name = std.get('s_name', 'Unknown')

            # --- LIVE STATUS UPDATE ---
            # প্রতিবার আপডেট করলে টেলিগ্রাম ব্লক করতে পারে, তাই প্রতি ১ জনে আপডেট করব এবং একটু থামব
            try:
                display_log = success_log[-200:] if len(success_log) > 200 else success_log # মেসেজ বেশি বড় হলে শেষের অংশ দেখাবে
                await status_msg.edit_text(
                    f"🔄 **Processing: {i+1}/{total}**\n"
                    f"🔨 Current: `{s_name}`\n\n"
                    f"📜 **Completed:**\n{display_log}",
                    parse_mode="Markdown"
                )
            except:
                pass # এডিট করতে না পারলে সমস্যা নেই, কাজ চলবে

            try:
                # টেমপ্লেট কপি
                doc_title = f"{s_name}_{std.get('s_id', 'Unknown')}"
                doc_copy = drive_service.files().copy(
                    fileId=template_id,
                    body={"name": doc_title}
                ).execute()
                
                # রিপ্লেসমেন্ট ডাটা প্রস্তুত করা
                requests = []
                # ১. কমন ডাটা
                for key, value in context.user_data.items():
                    if isinstance(value, str) and key not in ['is_batch_mode', 'target_batch', 'target_section']:
                        requests.append({
                            'replaceAllText': {
                                'containsText': {'text': f"{{{key}}}", 'matchCase': False},
                                'replaceText': value
                            }
                        })
                
                # ২. স্টুডেন্ট স্পেসিফিক ডাটা
                specific_fields = ['s_name', 's_id', 's_batch', 's_section', 'department']
                for field in specific_fields:
                    val = std.get(field, "N/A")
                    requests.append({
                        'replaceAllText': {
                            'containsText': {'text': f"{{{field}}}", 'matchCase': False},
                            'replaceText': val
                        }
                    })

                # গুগল ডক আপডেট
                if requests:
                    docs_service.documents().batchUpdate(
                        documentId=doc_copy['id'], body={'requests': requests}
                    ).execute()
                
                # PDF এক্সপোর্ট
                pdf_content = drive_service.files().export(
                    fileId=doc_copy['id'], mimeType="application/pdf"
                ).execute()
                
                # PDF সেভ (Temp Folder এ)
                safe_name = "".join([c for c in doc_title if c.isalpha() or c.isdigit() or c==' ' or c=='_']).strip()
                file_path = os.path.join(temp_dir, f"{safe_name}.pdf")
                
                with open(file_path, "wb") as f:
                    f.write(pdf_content)

                # --- NEW: সরাসরি স্টুডেন্টকে পাঠানো ---
                delivery_icon = "📂" # ডিফল্ট আইকন (যদি পাঠানো না যায়)
                try:
                    # নিজের (যে জেনারেট করছে) কাছে মেসেজ যাবে না, বাকিদের কাছে যাবে
                    if str(uid) != str(update.effective_user.id):
                        with open(file_path, "rb") as f_send:
                            await context.bot.send_document(
                                chat_id=uid,
                                document=f_send,
                                caption=f"📄 **Hello {s_name}!**\nHere is your cover page generated by CR/Admin.",
                                parse_mode="Markdown"
                            )
                        delivery_icon = "✅ Sent"
                    else:
                        delivery_icon = "👤 You"
                except Exception as send_e:
                    logger.error(f"Could not send to {s_name}: {send_e}")
                    delivery_icon = "⚠️ Not Sent" # ব্লক করা থাকলে বা সমস্যা হলে
                # ----------------------------------------
                
                # গুগল ড্রাইভ ক্লিনআপ
                drive_service.files().delete(fileId=doc_copy['id']).execute()
                
                generated_count += 1
                success_log += f"{delivery_icon} - {s_name}\n"
                
                # টেলিগ্রাম এপিআই লিমিট এড়াতে ১ সেকেন্ড বিরতি
                await asyncio.sleep(1) 
                
            except Exception as inner_e:
                logger.error(f"Failed for {s_name}: {inner_e}")
                success_log += f"❌ Failed - {s_name}\n"

        # ৪. জিপ ফাইল তৈরি
        await status_msg.edit_text("📦 **Packing all files into ZIP...**")
        zip_filename = f"Batch_{batch}_{sec}_{context.user_data.get('coursecode', 'Files')}.zip"
        
        shutil.make_archive(zip_filename.replace('.zip', ''), 'zip', temp_dir)
        
        # ৫. এডমিনকে জিপ পাঠানো
        caption = (
            f"✅ **Batch Process Completed**\n"
            f"🎓 Batch: {batch} | Sec: {sec}\n"
            f"📂 Generated: {generated_count}/{total}\n"
            f"ℹ️ 'Sent' means delivered to student's inbox."
        )
        
        with open(zip_filename, "rb") as f:
            await update.effective_chat.send_document(
                document=f,
                filename=zip_filename,
                caption=caption,
                parse_mode="Markdown"
            )

        # ৬. ক্লিনআপ
        try:
            shutil.rmtree(temp_dir)
            os.remove(zip_filename)
        except:
            pass
            
        log_cover_page(update.effective_user.id, f"BATCH_{batch}_{sec}")
        
        await update.effective_chat.send_message("✅ Task Finished!", reply_markup=MAIN_MENU_KEYBOARD)
        return MENU_SELECTION

    except Exception as e:
        logger.error(f"Batch Error: {e}")
        await status_msg.edit_text("❌ Critical Error in Batch Process.")
        return MENU_SELECTION

async def cancel(update: Update, context: CallbackContext) -> int:
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.delete_message()

    await update.effective_chat.send_message("🚫 Process cancelled.", reply_markup=MAIN_MENU_KEYBOARD)
    context.user_data.clear()
    return MENU_SELECTION

async def restart(update: Update, context: CallbackContext) -> int:
    await update.message.reply_text("🔄 Restarting...", reply_markup=MAIN_MENU_KEYBOARD)
    return await start(update, context)

async def help_command(update: Update, context: CallbackContext) -> None:
    help_text = (
        "🆘 **Help Guide**\n\n"
        "1. /start - Show Main Menu\n"
        "2. /cancel - Cancel current operation\n"
        "3. /restart - Restart the process.\n"
        "4. /admin - (Admin Only) Panel"
    )
    await update.message.reply_text(help_text, parse_mode="Markdown")

# ===== Batchwise PDF Logic =====

async def start_batch_pdf_flow(update: Update, context: CallbackContext) -> int:
    """Step 1: Scans user_data.json and asks for Batch selection."""
    user_id = update.effective_user.id
    
    # সেশন ক্লিয়ার এবং ফ্ল্যাগ সেট করা
    context.user_data.clear()
    context.user_data['is_batch_mode'] = True 
    
    # ১. JSON থেকে সব ব্যাচ খুঁজে বের করা
    try:
        if os.path.exists(USER_DATA_FILE):
            with open(USER_DATA_FILE, "r") as f:
                all_data = json.load(f)
        else:
            all_data = {}
    except:
        all_data = {}

    unique_batches = set()
    for uid, data in all_data.items():
        batch = data.get('s_batch')
        
        # --- FIX: শুধুমাত্র সংখ্যা হলে ব্যাচ হিসেবে নেবে ---
        # batch.isdigit() চেক করবে এটা শুধু সংখ্যা কিনা (যেমন: "62" = True, "bjhs" = False)
        if batch and batch.isdigit():
            unique_batches.add(batch)

    if not unique_batches:
        await update.message.reply_text(
            "❌ No valid batch data found in database!",
            reply_markup=MAIN_MENU_KEYBOARD
        )
        return MENU_SELECTION

    # ২. বাটন তৈরি
    keyboard = []
    # সুন্দর করে সাজানোর জন্য sort করা হলো (সংখ্যা হিসেবে)
    sorted_batches = sorted(list(unique_batches), key=int)
    
    row = []
    for batch in sorted_batches:
        row.append(InlineKeyboardButton(f"Batch {batch}", callback_data=f"batch_{batch}"))
        if len(row) == 3: # প্রতি লাইনে ৩টা করে বাটন
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
        
    keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel")])

    await update.message.reply_text(
        "📦 **Batchwise PDF Mode**\n\nSelect a **Batch** from the database:",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return BATCH_SELECT

async def select_batch_handler(update: Update, context: CallbackContext) -> int:
    """Step 2: Saves Batch and asks for Section."""
    query = update.callback_query
    await query.answer()

    if query.data == "cancel":
        return await cancel(update, context)

    selected_batch = query.data.split("_")[1]
    context.user_data['target_batch'] = selected_batch

    # ১. ওই ব্যাচের সেকশন খুঁজে বের করা
    with open(USER_DATA_FILE, "r") as f:
        all_data = json.load(f)

    unique_sections = set()
    for uid, data in all_data.items():
        if data.get('s_batch') == selected_batch and 's_section' in data:
            unique_sections.add(data['s_section'])

    # ২. বাটন তৈরি
    keyboard = []
    sorted_sections = sorted(list(unique_sections))
    
    row = []
    for sec in sorted_sections:
        row.append(InlineKeyboardButton(f"Sec {sec}", callback_data=f"sec_{sec}"))
        if len(row) == 3:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
        
    keyboard.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel")])

    await query.edit_message_text(
        f"✅ Selected Batch: **{selected_batch}**\n\nNow select a **Section**:",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return SECTION_SELECT

async def select_section_handler(update: Update, context: CallbackContext) -> int:
    """Step 3: Saves Section and jumps to Assignment/Lab selection."""
    query = update.callback_query
    await query.answer()

    if query.data == "cancel":
        return await cancel(update, context)

    selected_sec = query.data.split("_")[1]
    context.user_data['target_section'] = selected_sec

    # কাউন্ট চেক করা (কয়জন স্টুডেন্ট আছে)
    with open(USER_DATA_FILE, "r") as f:
        all_data = json.load(f)
    
    count = 0
    for uid, data in all_data.items():
        if data.get('s_batch') == context.user_data['target_batch'] and \
           data.get('s_section') == selected_sec:
            count += 1

    await query.edit_message_text(
        f"✅ Target: **Batch {context.user_data['target_batch']} - Section {selected_sec}**\n"
        f"👥 Total Students Found: `{count}`\n\n"
        f"Now, let's set up the Assignment details.",
        parse_mode="Markdown"
    )

    # এখন আমরা পুরানো ফ্লো-তে ফিরে যাব (Assignment/Lab selection)
    keyboard = [
        [InlineKeyboardButton("Assignment", callback_data='assignment')],
        [InlineKeyboardButton("Lab", callback_data='lab')],
        [InlineKeyboardButton("❌ Cancel", callback_data='cancel')]
    ]
    await query.message.reply_text(
        "Which cover page type?",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return COVER_PAGE_TYPE

# ===== Admin Functions =====

async def admin_start(update: Update, context: CallbackContext) -> int:
    """Starts the admin session."""
    user_id = str(update.effective_user.id)

    if user_id not in ADMIN_CHAT_IDS:
        await update.message.reply_text("🚫 Unauthorized Access.")
        return ConversationHandler.END

    await update.message.reply_text(
        "🔐 **Admin Panel Initialized**\nSelect an option:",
        parse_mode="Markdown",
        reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True, one_time_keyboard=True)
    )
    return ADMIN_HOME

async def admin_handle_menu(update: Update, context: CallbackContext) -> int:
    """Handles the button clicks in Admin Panel."""
    choice = update.message.text
    user_id = str(update.effective_user.id)

    # --- [NEW] Add CR Logic ---
    if choice == "➕ Add CR":
        await update.message.reply_text(
            "🆕 **Adding New CR**\n\n"
            "Please enter the **Telegram User ID** you want to promote to CR (Numbers only):\n"
            "(To cancel, type /cancel)",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardRemove()
        )
        return ADD_CR_ONLY_ID  # Sending to ID input state

    elif choice == "📢 Broadcast":
        await update.message.reply_text(
            "📝 **Broadcast Mode**\n\nEnter the message you want to send to all users (or type /cancel to go back):",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardRemove()
        )
        return ADMIN_BROADCAST_WAIT

    elif choice == "📊 Admin Report":
        # Report Generation Logic
        try:
            with open(VISITOR_LOG_FILE, "r") as f: v = json.load(f)
        except: v = []
        try:
            with open(COVER_PAGE_LOG_FILE, "r") as f: c = json.load(f)
        except: c = []

        unique_users = len({x.get("user_id") for x in v})
        total_covers = len(c)

        report = (
            f"📊 **System Report**\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"👥 Unique Visitors: `{unique_users}`\n"
            f"📄 Covers Generated: `{total_covers}`\n"
            f"📅 Server Time: `{datetime.now().strftime('%Y-%m-%d %H:%M')}`"
        )
        await update.message.reply_text(report, parse_mode="Markdown", reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True))
        return ADMIN_HOME

    elif choice == "🧑‍💬 Help User":
        await update.message.reply_text(
            "💡 **To reply to a user:**\nUse the command:\n`/help_user <user_id> <message>`",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True)
        )
        return ADMIN_HOME

    elif choice == "❌ Close Menu":
        await update.message.reply_text("🔐 Admin Panel Closed.", reply_markup=MAIN_MENU_KEYBOARD)
        return ConversationHandler.END

    else:
        await update.message.reply_text("⚠️ Invalid Option.", reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True))
        return ADMIN_HOME

async def save_cr_id_only(update: Update, context: CallbackContext) -> int:
    """Gets the ID and saves it to the CR list."""
    new_cr_id = update.message.text.strip()

    # 1. Validation: Is it a number?
    if not new_cr_id.isdigit():
        await update.message.reply_text("⚠️ ID must be numeric. Please try again or type /cancel.")
        return ADD_CR_ONLY_ID

    # 2. Load previous list
    cr_list = load_cr_list()

    # 3. Duplicate Check
    if new_cr_id in cr_list:
        await update.message.reply_text(
            f"⚠️ User ID `{new_cr_id}` is already in the CR list!",
            parse_mode="Markdown",
            reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True)
        )
        return ADMIN_HOME

    # 4. Save
    cr_list.append(new_cr_id)
    save_cr_list(cr_list)

    await update.message.reply_text(
        f"✅ **Success!**\nUser `{new_cr_id}` has been successfully promoted to CR.",
        parse_mode="Markdown",
        reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True)
    )
    return ADMIN_HOME

async def admin_broadcast_send(update: Update, context: CallbackContext) -> int:
    """Sends the broadcast message."""
    message = update.message.text

    if message == '/cancel':
        await update.message.reply_text("🚫 Broadcast Cancelled.", reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True))
        return ADMIN_HOME

    await update.message.reply_text("🚀 Sending Broadcast...")

    # Load users
    try:
        with open(VISITOR_LOG_FILE, "r") as f:
            visitors = json.load(f)
    except:
        visitors = []

    user_ids = list({v.get("user_id") for v in visitors if v.get("user_id")})
    sent_count = 0
    blocked_count = 0

    for uid in user_ids:
        try:
            await context.bot.send_message(chat_id=uid, text=f"📢 **Announcement:**\n\n{message}", parse_mode="Markdown")
            sent_count += 1
            await asyncio.sleep(0.05) # Rate limit safety
        except Exception:
            blocked_count += 1

    await update.message.reply_text(
        f"✅ **Broadcast Complete**\n"
        f"Sent to: {sent_count}\n"
        f"Failed/Blocked: {blocked_count}",
        parse_mode="Markdown",
        reply_markup=ReplyKeyboardMarkup(ADMIN_MENU_KEYS, resize_keyboard=True)
    )
    return ADMIN_HOME

async def admin_cancel(update: Update, context: CallbackContext) -> int:
    """Exits the admin conversation."""
    await update.message.reply_text("🔐 Admin Panel Closed.", reply_markup=MAIN_MENU_KEYBOARD)
    return ConversationHandler.END

async def help_user(update: Update, context: CallbackContext):
    if str(update.effective_chat.id) not in ADMIN_CHAT_IDS: return
    try:
        uid = int(context.args[0])
        msg = " ".join(context.args[1:])
        await context.bot.send_message(uid, f"🆘 Admin Support: {msg}")
        await update.message.reply_text("✅ Sent.")
    except:
        await update.message.reply_text("Usage: /help_user <id> <msg>")

async def broadcast(update: Update, context: CallbackContext):
    if str(update.effective_chat.id) not in ADMIN_CHAT_IDS: return
    await update.message.reply_text("Use Admin Panel for broadcast.")

async def post_init(application: Application) -> None:
    scheduler.start()
    logger.info("Scheduler started.")

async def error_handler(update: Update, context: CallbackContext) -> None:
    """Log the error and handle specific network errors gracefully."""
    
    # যদি সাধারণ নেটওয়ার্ক এরর হয়, তাহলে শুধু ওয়ার্নিং প্রিন্ট করবে (বিশাল এরর দেখাবে না)
    if isinstance(context.error, NetworkError):
        logger.warning(f"⚠️ Network Glitch: {context.error} (Bot will retry automatically)")
        return

    # অন্য যেকোনো এরর হলে বিস্তারিত লগ দেখাবে
    logger.error(msg="Exception while handling an update:", exc_info=context.error)

# ===== Main Execution =====

def main():
    """Run the bot."""
    global docs_service, drive_service

    # --- 1. Google Services Initialization ---
    try:
        ssl_context = ssl.create_default_context()
        ssl_context.check_hostname = False
        ssl_context.verify_mode = ssl.CERT_NONE

        creds = service_account.Credentials.from_service_account_file(
            SERVICE_ACCOUNT_FILE,
            scopes=SCOPES
        )

        docs_service = build('docs', 'v1', credentials=creds)
        drive_service = build('drive', 'v3', credentials=creds)
        logger.info("Google API services initialized successfully.")
    except Exception as e:
        logger.error(f"Failed to initialize Google API services: {e}")
        return

    # --- 2. Bot Application Setup (Updated for Stability) ---
    
    # নেটওয়ার্ক এরর কমানোর জন্য রিকোয়েস্ট সেটিংস
    t_request = HTTPXRequest(
        connection_pool_size=8,
        read_timeout=60,    # রিড টাইমআউট এখানে সেট করতে হবে
        write_timeout=60,   # রাইট টাইমআউট এখানে
        connect_timeout=60,
        pool_timeout=60
    )

    # application বিল্ড করার সময় request টি পাস করে দিতে হবে
    application = Application.builder().token(TELEGRAM_BOT_TOKEN).request(t_request).post_init(post_init).build()

    # --- 3. Conversation Handler Configuration ---

    # === Global Menu Handler ===
    menu_pattern = r"^(📄|👯|📦|👤|👥|📚|🗑|👨‍🏫|💬)"
    global_menu_handler = MessageHandler(filters.Regex(menu_pattern), menu_handler)

    # A. Admin Handler
    admin_conv_handler = ConversationHandler(
        entry_points=[CommandHandler('admin', admin_start)],
        states={
            ADMIN_HOME: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_handle_menu)],
            ADMIN_BROADCAST_WAIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, admin_broadcast_send)],
            
            # --- [NEW] নতুন স্টেট এখানে যুক্ত করা হলো ---
            ADD_CR_ONLY_ID: [MessageHandler(filters.TEXT & ~filters.COMMAND, save_cr_id_only)]
        },
        fallbacks=[CommandHandler('cancel', admin_cancel)],
    )

    # B. User Handler
    conv_handler = ConversationHandler(
        entry_points=[CommandHandler('start', start)],
        states={
            MENU_SELECTION: [MessageHandler(filters.TEXT & ~filters.COMMAND, menu_handler)],

            # --- Batch Mode States ---
            BATCH_SELECT: [CallbackQueryHandler(select_batch_handler), global_menu_handler],
            SECTION_SELECT: [CallbackQueryHandler(select_section_handler), global_menu_handler],

            # --- My Profile Actions ---
            MY_PROFILE_ACTION: [CallbackQueryHandler(my_profile_action), global_menu_handler],

            # --- Friend Profile Actions ---
            FRIEND_PROFILE_ACTION: [CallbackQueryHandler(friend_profile_action), global_menu_handler],

            ADD_FRIEND_NAME: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_friend_name)],
            ADD_FRIEND_ID: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_friend_id)],
            ADD_FRIEND_BATCH: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_friend_batch)],
            ADD_FRIEND_SECTION: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_friend_section)],

            ADD_FRIEND_DEPT: [
                global_menu_handler,
                # ফ্রেন্ড এড করার সময় ডিপার্টমেন্ট বাটন হ্যান্ডেল করা
                CallbackQueryHandler(add_friend_dept),
                # ম্যানুয়াল ইনপুটের জন্য টেক্সট হ্যান্ডলার
                MessageHandler(filters.TEXT & ~filters.COMMAND, add_friend_dept) 
            ],

            REMOVE_FRIEND_SELECT: [CallbackQueryHandler(remove_friend_handler), global_menu_handler],

            # --- PDF for Friend Selection ---
            SELECT_FRIEND_FOR_PDF: [CallbackQueryHandler(select_friend_for_pdf), global_menu_handler],

            # --- Course & Teacher Management ---
            ADD_COURSE_TITLE: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_course_title)],
            ADD_COURSE_CODE: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_course_code)],
            REMOVE_COURSE_SELECT: [CallbackQueryHandler(remove_course_handler), global_menu_handler],

            # --- Teacher Add Flow Fixes ---
            ADD_TEACHER_NAME: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_teacher_name)],
            ADD_TEACHER_DESIG: [CallbackQueryHandler(add_teacher_desig), global_menu_handler],
            ADD_TEACHER_DESIG_MANUAL: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_teacher_desig_manual)], # Fixed Handler
            ADD_TEACHER_DEPT: [CallbackQueryHandler(add_teacher_dept), global_menu_handler], # Fixed: Only Callback
            ADD_TEACHER_DEPT_MANUAL: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, add_teacher_dept_manual)], # New Manual Handler
            REMOVE_TEACHER_SELECT: [CallbackQueryHandler(remove_teacher_handler), global_menu_handler],

            # --- Feedback Handler ---
            FEEDBACK_INPUT: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, handle_feedback_message)],

            # --- Generation Flow ---
            COVER_PAGE_TYPE: [CallbackQueryHandler(cover_page_type), global_menu_handler],

            STUDENT_DEPARTMENT: [CallbackQueryHandler(student_department), global_menu_handler],
            OTHER_DEPARTMENT: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, other_department)],
            SELECT_SAVED_COURSE: [CallbackQueryHandler(select_saved_course), global_menu_handler],

            COURSE_TITLE: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, course_title)],
            COURSE_CODE: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, course_code)],
            EXPERIMENT_OR_ASSIGNMENT_NO: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, experiment_or_assignment_no)],
            EXPERIMENT_OR_ASSIGNMENT_TITLE: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, experiment_or_assignment_title)],

            S_NAME: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, s_name)],
            S_ID: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, s_id)],
            S_BATCH: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, s_batch)],
            S_SECTION: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, s_section)],

            SELECT_SAVED_TEACHER: [CallbackQueryHandler(select_saved_teacher), global_menu_handler],
            T_NAME: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, t_name)],
            
            # --- PDF Gen Teacher Flow Fixes ---
            T_DESIGNATION: [CallbackQueryHandler(t_designation), global_menu_handler],
            T_DESIGNATION_MANUAL: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, t_designation_manual)], 
            T_DEPARTMENT: [CallbackQueryHandler(t_department), global_menu_handler],
            T_DEPARTMENT_MANUAL: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, t_department_manual)],
            
            # Date Step
            DATE: [
                global_menu_handler,
                CallbackQueryHandler(handle_calendar_date, pattern="^cbcal_")
            ],

            CONFIRMATION: [CallbackQueryHandler(confirm_details), global_menu_handler],
            EDIT_FIELD: [CallbackQueryHandler(edit_field), global_menu_handler],
            EDIT_SINGLE_FIELD: [global_menu_handler, MessageHandler(filters.TEXT & ~filters.COMMAND, edit_single_field)]
        },
        fallbacks=[
            CommandHandler('cancel', cancel),
            CommandHandler('restart', restart),
            CommandHandler('help', help_command)
        ],
        allow_reentry=True
    )

    # --- 4. Add Handlers ---
    application.add_handler(admin_conv_handler)
    application.add_handler(conv_handler)

    # Commands
    application.add_handler(CommandHandler('help', help_command))
    application.add_handler(CommandHandler('help_user', help_user))
    
    # --- NEW: CR Adding Command ---
    application.add_handler(CommandHandler('add_cr', add_cr_command))

    # Errors
    application.add_error_handler(error_handler)
    
    # --- 5. Start Polling ---
    logger.info("Starting the bot...")
    
    # এখানে আর read_timeout/write_timeout দেওয়া যাবে না, কারণ ওটা উপরে HTTPXRequest এ দেওয়া হয়েছে
    application.run_polling(
        poll_interval=2.0,
        timeout=30
    )

if __name__ == "__main__":
    main()
