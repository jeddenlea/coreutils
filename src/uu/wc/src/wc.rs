//  * This file is part of the uutils coreutils package.
//  *
//  * (c) Boden Garman <bpgarman@gmail.com>
//  *
//  * For the full copyright and license information, please view the LICENSE
//  * file that was distributed with this source code.

// cSpell:ignore wc wc's

mod count_fast;
mod countable;
mod word_count;

use std::{
    borrow::Cow,
    cmp::max,
    ffi::{OsStr, OsString},
    fmt::Display,
    fs::{self, File},
    io::{self, Write},
    iter,
    path::{Path, PathBuf},
};

use clap::{builder::ValueParser, crate_version, Arg, ArgAction, ArgMatches, Command};
use thiserror::Error;
use unicode_width::UnicodeWidthChar;
use utf8::{BufReadDecoder, BufReadDecoderError};

use uucore::{
    error::{FromIo, UError, UIoError, UResult, USimpleError},
    format_usage, help_about, help_usage,
    quoting_style::{escape_name, QuotingStyle},
    show,
};

use crate::{
    count_fast::{count_bytes_chars_and_lines_fast, count_bytes_fast},
    countable::WordCountable,
    word_count::WordCount,
};

/// The minimum character width for formatting counts when reading from stdin.
const MINIMUM_WIDTH: usize = 7;

struct Settings {
    show_bytes: bool,
    show_chars: bool,
    show_lines: bool,
    show_words: bool,
    show_max_line_length: bool,
}

impl Default for Settings {
    fn default() -> Self {
        // Defaults if none of -c, -m, -l, -w, nor -L are specified.
        Self {
            show_bytes: true,
            show_chars: false,
            show_lines: true,
            show_words: true,
            show_max_line_length: false,
        }
    }
}

impl Settings {
    fn new(matches: &ArgMatches) -> Self {
        let settings = Self {
            show_bytes: matches.get_flag(options::BYTES),
            show_chars: matches.get_flag(options::CHAR),
            show_lines: matches.get_flag(options::LINES),
            show_words: matches.get_flag(options::WORDS),
            show_max_line_length: matches.get_flag(options::MAX_LINE_LENGTH),
        };

        if settings.number_enabled() > 0 {
            settings
        } else {
            Default::default()
        }
    }

    fn number_enabled(&self) -> u32 {
        [
            self.show_bytes,
            self.show_chars,
            self.show_lines,
            self.show_max_line_length,
            self.show_words,
        ]
        .into_iter()
        .map(Into::<u32>::into)
        .sum()
    }
}

const ABOUT: &str = help_about!("wc.md");
const USAGE: &str = help_usage!("wc.md");

mod options {
    pub static BYTES: &str = "bytes";
    pub static CHAR: &str = "chars";
    pub static FILES0_FROM: &str = "files0-from";
    pub static LINES: &str = "lines";
    pub static MAX_LINE_LENGTH: &str = "max-line-length";
    pub static WORDS: &str = "words";
}
static ARG_FILES: &str = "files";
static STDIN_REPR: &str = "-";

static QS_ESCAPE: &QuotingStyle = &QuotingStyle::Shell {
    escape: true,
    always_quote: false,
    show_control: false,
};
static QS_QUOTE_ESCAPE: &QuotingStyle = &QuotingStyle::Shell {
    escape: true,
    always_quote: true,
    show_control: false,
};

/// Supported inputs.
enum Inputs {
    /// Default Standard input, i.e. no arguments.
    Stdin,
    /// Files; "-" means stdin, possibly multiple times!
    Paths(Vec<OsString>),
    /// --files0-from; "-" means stdin.
    Files0From(OsString),
}

impl Inputs {
    fn new(matches: &ArgMatches) -> UResult<Self> {
        let arg_files = matches.get_many::<OsString>(ARG_FILES);
        let files0_from = matches.get_one::<OsString>(options::FILES0_FROM);

        match (arg_files, files0_from) {
            (None, None) => Ok(Self::Stdin),
            (Some(files), None) => Ok(Self::Paths(files.cloned().collect())),
            (None, Some(path)) => Ok(Self::Files0From(path.into())),
            (Some(_), Some(_)) => Err(WcError::FilesDisabled.into()),
        }
    }
}

enum StdinKind {
    /// Specified on command-line with "-" (STDIN_REPR)
    Explicit,
    /// Implied by the lack of any arguments
    Implicit,
}

/// Represents a single input.
enum Input<'a> {
    Path(Cow<'a, Path>),
    Stdin(StdinKind),
}

impl Input<'_> {
    /// Converts input to title that appears in stats.
    fn to_title(&self) -> Option<Cow<str>> {
        match self {
            Self::Path(path) => Some(match path.to_str() {
                Some(s) if !s.contains('\n') => Cow::Borrowed(s),
                _ => Cow::Owned(escape_name(path.as_os_str(), QS_ESCAPE)),
            }),
            Self::Stdin(StdinKind::Explicit) => Some(Cow::Borrowed(STDIN_REPR)),
            Self::Stdin(StdinKind::Implicit) => None,
        }
    }

    /// Converts input into the form that appears in errors.
    fn path_display(&self) -> Cow<'static, str> {
        match self {
            Self::Path(path) => escape_name(OsStr::new(path.as_ref()), QS_ESCAPE).into(),
            Self::Stdin(_) => Cow::Borrowed("standard input"),
        }
    }
}

#[derive(Debug, Error)]
enum WcError {
    #[error("file operands cannot be combined with --files0-from")]
    FilesDisabled,
    #[error("when reading file names from stdin, no file name of '-' allowed")]
    StdinReprNotAllowed,
    #[error("invalid zero-length file name")]
    ZeroLengthFileName,
    #[error("{path}:{idx}: invalid zero-length file name")]
    ZeroLengthFileNameCtx { path: String, idx: usize },
}

impl UError for WcError {
    fn usage(&self) -> bool {
        matches!(self, Self::FilesDisabled)
    }
}

impl WcError {
    fn zero_len(ctx: Option<(String, usize)>) -> Self {
        match ctx {
            Some((path, idx)) => Self::ZeroLengthFileNameCtx { path, idx },
            None => Self::ZeroLengthFileName,
        }
    }
}

#[uucore::main]
pub fn uumain(args: impl uucore::Args) -> UResult<()> {
    let matches = uu_app().try_get_matches_from(args)?;

    let settings = Settings::new(&matches);
    let inputs = Inputs::new(&matches)?;

    wc(&inputs, &settings)
}

pub fn uu_app() -> Command {
    Command::new(uucore::util_name())
        .version(crate_version!())
        .about(ABOUT)
        .override_usage(format_usage(USAGE))
        .infer_long_args(true)
        .arg(
            Arg::new(options::BYTES)
                .short('c')
                .long(options::BYTES)
                .help("print the byte counts")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::CHAR)
                .short('m')
                .long(options::CHAR)
                .help("print the character counts")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::FILES0_FROM)
                .long(options::FILES0_FROM)
                .value_name("F")
                .help(concat!(
                    "read input from the files specified by\n",
                    "  NUL-terminated names in file F;\n",
                    "  If F is - then read names from standard input"
                ))
                .value_parser(ValueParser::os_string())
                .value_hint(clap::ValueHint::FilePath),
        )
        .arg(
            Arg::new(options::LINES)
                .short('l')
                .long(options::LINES)
                .help("print the newline counts")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::MAX_LINE_LENGTH)
                .short('L')
                .long(options::MAX_LINE_LENGTH)
                .help("print the length of the longest line")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(options::WORDS)
                .short('w')
                .long(options::WORDS)
                .help("print the word counts")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new(ARG_FILES)
                .action(ArgAction::Append)
                .value_parser(ValueParser::os_string())
                .value_hint(clap::ValueHint::FilePath),
        )
}

fn word_count_from_reader<T: WordCountable>(
    mut reader: T,
    settings: &Settings,
) -> (WordCount, Option<io::Error>) {
    match (
        settings.show_bytes,
        settings.show_chars,
        settings.show_lines,
        settings.show_max_line_length,
        settings.show_words,
    ) {
        // Specialize scanning loop to improve the performance.
        (false, false, false, false, false) => unreachable!(),

        // show_bytes
        (true, false, false, false, false) => {
            // Fast path when only show_bytes is true.
            let (bytes, error) = count_bytes_fast(&mut reader);
            (
                WordCount {
                    bytes,
                    ..WordCount::default()
                },
                error,
            )
        }

        // Fast paths that can be computed without Unicode decoding.
        // show_lines
        (false, false, true, false, false) => {
            count_bytes_chars_and_lines_fast::<_, false, false, true>(&mut reader)
        }
        // show_chars
        (false, true, false, false, false) => {
            count_bytes_chars_and_lines_fast::<_, false, true, false>(&mut reader)
        }
        // show_chars, show_lines
        (false, true, true, false, false) => {
            count_bytes_chars_and_lines_fast::<_, false, true, true>(&mut reader)
        }
        // show_bytes, show_lines
        (true, false, true, false, false) => {
            count_bytes_chars_and_lines_fast::<_, true, false, true>(&mut reader)
        }
        // show_bytes, show_chars
        (true, true, false, false, false) => {
            count_bytes_chars_and_lines_fast::<_, true, true, false>(&mut reader)
        }
        // show_bytes, show_chars, show_lines
        (true, true, true, false, false) => {
            count_bytes_chars_and_lines_fast::<_, true, true, true>(&mut reader)
        }
        // show_words
        (_, false, false, false, true) => {
            word_count_from_reader_specialized::<_, false, false, false, true>(reader)
        }
        // show_max_line_length
        (_, false, false, true, false) => {
            word_count_from_reader_specialized::<_, false, false, true, false>(reader)
        }
        // show_max_line_length, show_words
        (_, false, false, true, true) => {
            word_count_from_reader_specialized::<_, false, false, true, true>(reader)
        }
        // show_chars, show_words
        (_, false, true, false, true) => {
            word_count_from_reader_specialized::<_, false, true, false, true>(reader)
        }
        // show_chars, show_lines
        (_, false, true, true, false) => {
            word_count_from_reader_specialized::<_, false, true, true, false>(reader)
        }
        // show_lines, show_max_line_length, show_words
        (_, false, true, true, true) => {
            word_count_from_reader_specialized::<_, false, true, true, true>(reader)
        }
        // show_chars, show_words
        (_, true, false, false, true) => {
            word_count_from_reader_specialized::<_, true, false, false, true>(reader)
        }
        // show_chars, show_max_line_length
        (_, true, false, true, false) => {
            word_count_from_reader_specialized::<_, true, false, true, false>(reader)
        }
        // show_chars, show_max_line_length, show_words
        (_, true, false, true, true) => {
            word_count_from_reader_specialized::<_, true, false, true, true>(reader)
        }
        // show_chars, show_lines, show_words
        (_, true, true, false, true) => {
            word_count_from_reader_specialized::<_, true, true, false, true>(reader)
        }
        // show_chars, show_lines, show_max_line_length
        (_, true, true, true, false) => {
            word_count_from_reader_specialized::<_, true, true, true, false>(reader)
        }
        // show_chars, show_lines, show_max_line_length, show_words
        (_, true, true, true, true) => {
            word_count_from_reader_specialized::<_, true, true, true, true>(reader)
        }
    }
}

fn word_count_from_reader_specialized<
    T: WordCountable,
    const SHOW_CHARS: bool,
    const SHOW_LINES: bool,
    const SHOW_MAX_LINE_LENGTH: bool,
    const SHOW_WORDS: bool,
>(
    reader: T,
) -> (WordCount, Option<io::Error>) {
    let mut total = WordCount::default();
    let mut reader = BufReadDecoder::new(reader.buffered());
    let mut in_word = false;
    let mut current_len = 0;

    while let Some(chunk) = reader.next_strict() {
        match chunk {
            Ok(text) => {
                for ch in text.chars() {
                    if SHOW_WORDS {
                        if ch.is_whitespace() {
                            in_word = false;
                        } else if ch.is_ascii_control() {
                            // These count as characters but do not affect the word state
                        } else if !in_word {
                            in_word = true;
                            total.words += 1;
                        }
                    }
                    if SHOW_MAX_LINE_LENGTH {
                        match ch {
                            '\n' | '\r' | '\x0c' => {
                                total.max_line_length = max(current_len, total.max_line_length);
                                current_len = 0;
                            }
                            '\t' => {
                                current_len -= current_len % 8;
                                current_len += 8;
                            }
                            _ => {
                                current_len += ch.width().unwrap_or(0);
                            }
                        }
                    }
                    if SHOW_LINES && ch == '\n' {
                        total.lines += 1;
                    }
                    if SHOW_CHARS {
                        total.chars += 1;
                    }
                }
                total.bytes += text.len();
            }
            Err(BufReadDecoderError::InvalidByteSequence(bytes)) => {
                // GNU wc treats invalid data as neither word nor char nor whitespace,
                // so no other counters are affected
                total.bytes += bytes.len();
            }
            Err(BufReadDecoderError::Io(e)) => {
                return (total, Some(e));
            }
        }
    }

    total.max_line_length = max(current_len, total.max_line_length);

    (total, None)
}

enum CountResult {
    /// Nothing went wrong.
    Success(WordCount),
    /// Managed to open but failed to read.
    Interrupted(WordCount, UIoError),
    /// Didn't even manage to open.
    Failure(UIoError),
}

/// If we fail opening a file, we only show the error. If we fail reading the
/// file, we show a count for what we managed to read.
///
/// Therefore, the reading implementations always return a total and sometimes
/// return an error: (WordCount, Option<io::Error>).
fn word_count_from_input(input: &Input<'_>, settings: &Settings) -> CountResult {
    let (total, maybe_err) = match input {
        Input::Stdin(_) => word_count_from_reader(io::stdin().lock(), settings),
        Input::Path(path) => match File::open(path) {
            Ok(f) => word_count_from_reader(f, settings),
            Err(err) => return CountResult::Failure(err.into()),
        },
    };
    match maybe_err {
        None => CountResult::Success(total),
        Some(err) => CountResult::Interrupted(total, err.into()),
    }
}

/// Compute the number of digits needed to represent all counts in all inputs.
///
/// For [`Inputs::Stdin`], [`MINIMUM_WIDTH`] is returned, unless there is only one counter number
/// to be printed, in which case 1 is returned.
///
/// For [`Inputs::Files0From`], [`MINIMUM_WIDTH`] is returned.
///
/// An [`Inputs::Paths`] may include zero or more "-" entries, each of which represents reading
/// from `stdin`. The presence of any such entry causes this function to return a width that is at
/// least [`MINIMUM_WIDTH`].
///
/// If an [`Inputs::Paths`] contains only one path and only one number needs to be printed then
/// this function is optimized to return 1 without making any calls to get file metadata.
///
/// If file metadata could not be read from any of the [`Input::Path`] input, that input does not
/// affect number width computation.  Otherwise, the file sizes from the files' metadata are summed
/// and the number of digits in that total size is returned.
fn compute_number_width(inputs: &Inputs, settings: &Settings) -> usize {
    match inputs {
        Inputs::Stdin if settings.number_enabled() == 1 => 1,
        Inputs::Stdin => MINIMUM_WIDTH,
        Inputs::Files0From(_) => 1,
        Inputs::Paths(paths) => {
            if settings.number_enabled() == 1 && paths.len() == 1 {
                return 1;
            }

            let mut minimum_width = 1;
            let mut total: u64 = 0;
            for path in paths.iter() {
                if path == STDIN_REPR {
                    minimum_width = MINIMUM_WIDTH;
                    continue;
                }
                if let Ok(meta) = fs::metadata(path) {
                    if meta.is_file() {
                        total += meta.len();
                    } else {
                        minimum_width = MINIMUM_WIDTH;
                    }
                }
            }

            if total == 0 {
                minimum_width
            } else {
                let total_width = (1 + total.ilog10())
                    .try_into()
                    .expect("ilog of one usize should fit into a usize");
                max(total_width, minimum_width)
            }
        }
    }
}

enum InputError {
    Io(UIoError),
    Wc(WcError),
}

impl From<WcError> for InputError {
    fn from(e: WcError) -> Self {
        Self::Wc(e)
    }
}

impl From<io::Error> for InputError {
    fn from(e: io::Error) -> Self {
        Self::Io(e.into())
    }
}

impl Display for InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Wc(e) => e.fmt(f),
        }
    }
}

type InputIterItem<'a> = Result<Input<'a>, InputError>;

impl Inputs {
    // Creates an iterator which yields values borrowed from the command line arguments.
    // Returns an error if the file specified in --files0-from cannot be opened.
    fn try_iter(&self) -> UResult<impl Iterator<Item = InputIterItem>> {
        let base: Box<dyn Iterator<Item = _>> = match self {
            Self::Stdin => Box::new(iter::once(Ok(Input::Stdin(StdinKind::Implicit)))),
            Self::Paths(paths) => Box::new(paths.iter().map(|p| {
                Ok(match p {
                    p if p == STDIN_REPR => Input::Stdin(StdinKind::Explicit),
                    p => Input::Path(Cow::Borrowed(p.as_ref())),
                })
            })),
            Self::Files0From(path) if path == STDIN_REPR => Box::new(files0_iter_stdin()),
            Self::Files0From(path) => Box::new(files0_iter_file(path)?),
        };

        // The index of each yielded item must be tracked for error reporting.
        let mut with_idx = base.enumerate();
        let path = match self {
            Self::Files0From(path) => Some(path),
            _ => None,
        };

        let iter = iter::from_fn(move || {
            let (idx, next) = with_idx.next()?;
            match next {
                // filter zero length file names...
                Ok(Input::Path(p)) if p.as_os_str().is_empty() => Some(Err(InputError::Wc(
                    WcError::zero_len(path.map(|p| (escape_name(p, QS_ESCAPE), idx))),
                ))),
                _ => Some(next),
            }
        });
        Ok(iter)
    }
}

/// To be used with `--files0-from=-`, this applies a filter on the results of files0_iter to
/// translate '-' into the appropriate error.
fn files0_iter_stdin<'a>() -> impl Iterator<Item = InputIterItem<'a>> {
    files0_iter(io::stdin().lock()).map(|i| match i {
        Ok(Input::Stdin(_)) => Err(WcError::StdinReprNotAllowed.into()),
        _ => i,
    })
}

fn files0_iter_file<'a>(path: &OsStr) -> UResult<impl Iterator<Item = InputIterItem<'a>>> {
    match File::open(path) {
        Ok(f) => Ok(files0_iter(f)),
        Err(e) => Err(e.map_err_context(|| {
            format!(
                "cannot open {} for reading",
                escape_name(path, QS_QUOTE_ESCAPE)
            )
        })),
    }
}

fn files0_iter<'a>(r: impl io::Read + 'static) -> impl Iterator<Item = InputIterItem<'a>> {
    use std::io::BufRead;
    io::BufReader::new(r).split(b'\0').map(|res| match res {
        Ok(p) if p == STDIN_REPR.as_bytes() => Ok(Input::Stdin(StdinKind::Explicit)),
        Ok(p) => {
            // Unix systems have OsStrings which are simply strings of bytes, not necesarily UTF-8.
            #[cfg(unix)]
            {
                use std::os::unix::ffi::OsStringExt;
                Ok(Input::Path(PathBuf::from(OsString::from_vec(p)).into()))
            }

            // ...Windows does not, we must go through Strings.
            #[cfg(not(unix))]
            {
                let s =
                    String::from_utf8(p).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
                Ok(Input::Path(PathBuf::from(s).into()))
            }
        }
        Err(e) => Err(e.into()),
    })
}

/// shorthand for `show!(USimpleError::new(...))`, works just like `format!`.
macro_rules! record_error {
    ($fmt:literal $(, $arg:expr)*) => {
        show!(USimpleError::new(
            1,
            format!($fmt $(, $arg)*)
        ));
    }
}

fn wc(inputs: &Inputs, settings: &Settings) -> UResult<()> {
    let number_width = compute_number_width(inputs, settings);

    let mut total_word_count = WordCount::default();
    let mut num_inputs = 0u32;

    for maybe_input in inputs.try_iter()? {
        num_inputs = num_inputs.saturating_add(1);

        let input = match maybe_input {
            Ok(input) => input,
            Err(err) => {
                record_error!("{err}");
                continue;
            }
        };

        let word_count = match word_count_from_input(&input, settings) {
            CountResult::Success(word_count) => word_count,
            CountResult::Interrupted(word_count, err) => {
                record_error!("{}: {}", input.path_display(), err);
                word_count
            }
            CountResult::Failure(err) => {
                record_error!("{}: {}", input.path_display(), err);
                continue;
            }
        };
        total_word_count += word_count;
        let maybe_title = input.to_title();
        let maybe_title_str = maybe_title.as_deref();
        if let Err(err) = print_stats(settings, &word_count, maybe_title_str, number_width) {
            let title = maybe_title_str.unwrap_or("<stdin>");
            record_error!("failed to print result for {title}: {err}");
        }
    }

    if num_inputs > 1 {
        if let Err(err) = print_stats(settings, &total_word_count, Some("total"), number_width) {
            record_error!("failed to print total: {err}");
        }
    }

    // Although this appears to be returning `Ok`, the exit code may
    // have been set to a non-zero value by a call to `show!()` above.
    Ok(())
}

fn print_stats(
    settings: &Settings,
    result: &WordCount,
    title: Option<&str>,
    number_width: usize,
) -> io::Result<()> {
    let mut stdout = io::stdout().lock();

    let mut space = "";

    macro_rules! print_column {
        ($s:ident, $c:ident) => {
            if settings.$s {
                write!(stdout, "{space}{:width$}", result.$c, width = number_width)?;
                #[allow(unused_assignments)]
                {
                    space = " ";
                }
            }
        };
    }

    print_column!(show_lines, lines);
    print_column!(show_words, words);
    print_column!(show_chars, chars);
    print_column!(show_bytes, bytes);
    print_column!(show_max_line_length, max_line_length);

    if let Some(title) = title {
        writeln!(stdout, "{space}{title}")
    } else {
        writeln!(stdout)
    }
}
