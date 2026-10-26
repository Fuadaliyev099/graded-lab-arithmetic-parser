/*
 * Name: Fuad Aliyev
 * Student ID: 251ADB065
 * Assignment: Graded Lab - Arithmetic Parser in C
 *
 * AI/resource disclosure: OpenAI ChatGPT assisted with the design and draft
 * of the recursive-descent parser, checked arithmetic, and command-line/file
 * handling. Prompt summary: "Help me implement a C arithmetic parser that
 * follows the RTU lab specification and supplied tests." Review and adapt this
 * code so this disclosure accurately describes the assistance actually used.
 *
 * The parser uses one function per precedence level. This makes precedence and
 * associativity explicit, and it reports errors using byte positions counted
 * from the start of the whole input file (including blank/comment lines).
 */

#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

/* Update the student ID before submitting. These strings are used in output names. */
#define STUDENT_FIRST_NAME "fuad"
#define STUDENT_LAST_NAME  "aliyev"
#define STUDENT_ID         "251ADB065"

#define MAX_PARSE_DEPTH 256U

typedef struct {
    long long integer_value;
    double real_value;
    bool is_real;
    size_t start_position; /* 1-based position of this value in the original file */
} Value;

typedef struct {
    const char *line;
    size_t length;
    size_t position;
    size_t file_offset; /* zero-based offset where this line begins */
    size_t error_position;
    unsigned int depth;
    bool failed;
} Parser;

typedef struct {
    char *data;
    size_t length;
    size_t capacity;
} StringBuilder;

static size_t current_position(const Parser *parser)
{
    if (parser->position < parser->length) {
        return parser->file_offset + parser->position + 1U;
    }
    /* At line end, report the newline's position, or one past EOF. */
    return parser->file_offset + parser->length + 1U;
}

static void set_error(Parser *parser, size_t position)
{
    if (!parser->failed) {
        parser->failed = true;
        parser->error_position = position;
    }
}

static void error_at_current(Parser *parser)
{
    set_error(parser, current_position(parser));
}

static void skip_spaces(Parser *parser)
{
    while (parser->position < parser->length &&
           isspace((unsigned char)parser->line[parser->position])) {
        parser->position++;
    }
}

static bool checked_add(long long left, long long right, long long *result)
{
    if ((right > 0 && left > LLONG_MAX - right) ||
        (right < 0 && left < LLONG_MIN - right)) {
        return false;
    }
    *result = left + right;
    return true;
}

static bool checked_subtract(long long left, long long right, long long *result)
{
    if ((right < 0 && left > LLONG_MAX + right) ||
        (right > 0 && left < LLONG_MIN + right)) {
        return false;
    }
    *result = left - right;
    return true;
}

static bool checked_multiply(long long left, long long right, long long *result)
{
    if (left == 0 || right == 0) {
        *result = 0;
        return true;
    }

    if (left == -1) {
        if (right == LLONG_MIN) {
            return false;
        }
        *result = -right;
        return true;
    }
    if (right == -1) {
        if (left == LLONG_MIN) {
            return false;
        }
        *result = -left;
        return true;
    }

    if (left > 0) {
        if ((right > 0 && left > LLONG_MAX / right) ||
            (right < 0 && right < LLONG_MIN / left)) {
            return false;
        }
    } else {
        if ((right > 0 && left < LLONG_MIN / right) ||
            (right < 0 && left < LLONG_MAX / right)) {
            return false;
        }
    }

    *result = left * right;
    return true;
}

static bool checked_integer_power(long long base, long long exponent,
                                 long long *result)
{
    long long answer = 1;
    long long factor = base;
    unsigned long long remaining = (unsigned long long)exponent;

    /* Exponentiation by squaring avoids a loop proportional to the exponent. */
    while (remaining > 0U) {
        if ((remaining & 1U) != 0U && !checked_multiply(answer, factor, &answer)) {
            return false;
        }
        remaining >>= 1U;
        if (remaining > 0U && !checked_multiply(factor, factor, &factor)) {
            return false;
        }
    }

    *result = answer;
    return true;
}

static Value make_integer(long long integer_value, size_t start_position)
{
    Value value;
    value.integer_value = integer_value;
    value.real_value = (double)integer_value;
    value.is_real = false;
    value.start_position = start_position;
    return value;
}

static Value make_real(double real_value, size_t start_position)
{
    Value value;
    value.integer_value = 0;
    value.real_value = real_value;
    value.is_real = true;
    value.start_position = start_position;
    return value;
}

static double as_double(Value value)
{
    return value.is_real ? value.real_value : (double)value.integer_value;
}

static Value parse_additive(Parser *parser);
static Value parse_power(Parser *parser);

static Value parse_primary(Parser *parser)
{
    Value value = make_integer(0, current_position(parser));
    size_t start;
    char character;

    skip_spaces(parser);
    start = current_position(parser);
    if (parser->failed) {
        return value;
    }
    if (parser->position >= parser->length) {
        error_at_current(parser);
        return value;
    }

    character = parser->line[parser->position];
    if (character == '(') {
        parser->position++;
        parser->depth++;
        if (parser->depth > MAX_PARSE_DEPTH) {
            set_error(parser, start);
            parser->depth--;
            return value;
        }

        value = parse_additive(parser);
        skip_spaces(parser);
        if (!parser->failed) {
            if (parser->position >= parser->length ||
                parser->line[parser->position] != ')') {
                error_at_current(parser);
            } else {
                parser->position++;
                /* Keep '(' as the start: division-by-zero points to its operand. */
                value.start_position = start;
            }
        }
        parser->depth--;
        return value;
    }

    if (!isdigit((unsigned char)character)) {
        /* Unary +/- and leading decimal points are intentionally not supported. */
        error_at_current(parser);
        return value;
    }

    {
        size_t digits_start = parser->position;
        bool has_decimal = false;

        while (parser->position < parser->length &&
               isdigit((unsigned char)parser->line[parser->position])) {
            parser->position++;
        }
        if (parser->position < parser->length &&
            parser->line[parser->position] == '.') {
            has_decimal = true;
            parser->position++;
            if (parser->position >= parser->length ||
                !isdigit((unsigned char)parser->line[parser->position])) {
                set_error(parser, parser->file_offset + parser->position);
                return value;
            }
            while (parser->position < parser->length &&
                   isdigit((unsigned char)parser->line[parser->position])) {
                parser->position++;
            }
        }

        {
            size_t token_length = parser->position - digits_start;
            char *token = malloc(token_length + 1U);
            if (token == NULL) {
                set_error(parser, parser->file_offset + digits_start + 1U);
                return value;
            }
            memcpy(token, parser->line + digits_start, token_length);
            token[token_length] = '\0';

            if (has_decimal) {
                char *end_pointer = NULL;
                double number;
                errno = 0;
                number = strtod(token, &end_pointer);
                if (errno == ERANGE || end_pointer != token + token_length ||
                    !isfinite(number)) {
                    free(token);
                    set_error(parser, parser->file_offset + digits_start + 1U);
                    return value;
                }
                value = make_real(number, parser->file_offset + digits_start + 1U);
            } else {
                char *end_pointer = NULL;
                long long number;
                errno = 0;
                number = strtoll(token, &end_pointer, 10);
                if (errno == ERANGE || end_pointer != token + token_length) {
                    free(token);
                    set_error(parser, parser->file_offset + digits_start + 1U);
                    return value;
                }
                value = make_integer(number, parser->file_offset + digits_start + 1U);
            }
            free(token);
        }
    }

    return value;
}

static Value apply_power(Parser *parser, Value left, Value right,
                         size_t operator_position)
{
    if ((right.is_real && right.real_value < 0.0) ||
        (!right.is_real && right.integer_value < 0)) {
        /* A negative exponent is reported at the start of the exponent expression. */
        set_error(parser, right.start_position);
        return left;
    }

    if (!left.is_real && !right.is_real) {
        long long result;
        if (!checked_integer_power(left.integer_value, right.integer_value, &result)) {
            set_error(parser, operator_position);
            return left;
        }
        return make_integer(result, left.start_position);
    }

    {
        double result = pow(as_double(left), as_double(right));
        /* NaN (for example, a negative base to a fractional power) is invalid. */
        if (!isfinite(result)) {
            set_error(parser, operator_position);
            return left;
        }
        return make_real(result, left.start_position);
    }
}

static Value parse_power(Parser *parser)
{
    Value left = parse_primary(parser);

    if (parser->failed) {
        return left;
    }
    skip_spaces(parser);
    if (parser->position + 1U < parser->length &&
        parser->line[parser->position] == '*' &&
        parser->line[parser->position + 1U] == '*') {
        size_t operator_position = current_position(parser);
        Value right;
        parser->position += 2U;
        parser->depth++;
        if (parser->depth > MAX_PARSE_DEPTH) {
            set_error(parser, operator_position);
            parser->depth--;
            return left;
        }
        /* Recursive RHS makes exponentiation right-associative: 2 ** 3 ** 2 = 512. */
        right = parse_power(parser);
        parser->depth--;
        if (parser->failed) {
            return left;
        }
        return apply_power(parser, left, right, operator_position);
    }
    return left;
}

static Value apply_multiplicative(Parser *parser, Value left, Value right,
                                  char operator, size_t operator_position,
                                  size_t right_start_position)
{
    if (operator == '/' &&
        ((right.is_real && right.real_value == 0.0) ||
         (!right.is_real && right.integer_value == 0))) {
        set_error(parser, right_start_position);
        return left;
    }

    if (!left.is_real && !right.is_real) {
        long long result;
        bool valid = true;

        if (operator == '*') {
            valid = checked_multiply(left.integer_value, right.integer_value, &result);
        } else if (operator == '/') {
            if (left.integer_value == LLONG_MIN && right.integer_value == -1) {
                valid = false;
            } else {
                result = left.integer_value / right.integer_value;
            }
        } else {
            return left;
        }

        if (!valid) {
            set_error(parser, operator_position);
            return left;
        }
        return make_integer(result, left.start_position);
    }

    {
        double left_number = as_double(left);
        double right_number = as_double(right);
        double result = operator == '*' ? left_number * right_number
                                        : left_number / right_number;
        if (!isfinite(result)) {
            set_error(parser, operator_position);
            return left;
        }
        return make_real(result, left.start_position);
    }
}

static Value parse_multiplicative(Parser *parser)
{
    Value left = parse_power(parser);

    while (!parser->failed) {
        char operator;
        size_t operator_position;
        size_t right_start_position;
        Value right;

        skip_spaces(parser);
        if (parser->position >= parser->length) {
            break;
        }

        operator = parser->line[parser->position];
        if (operator != '*' && operator != '/') {
            break;
        }
        /* ** belongs to parse_power, not multiplication. */
        if (operator == '*' && parser->position + 1U < parser->length &&
            parser->line[parser->position + 1U] == '*') {
            break;
        }

        operator_position = current_position(parser);
        parser->position++;
        skip_spaces(parser);
        right_start_position = current_position(parser);
        right = parse_power(parser);
        if (parser->failed) {
            break;
        }
        left = apply_multiplicative(parser, left, right, operator,
                                    operator_position, right_start_position);
    }

    return left;
}

static Value apply_additive(Parser *parser, Value left, Value right,
                            char operator, size_t operator_position)
{
    if (!left.is_real && !right.is_real) {
        long long result;
        bool valid = operator == '+'
                         ? checked_add(left.integer_value, right.integer_value, &result)
                         : checked_subtract(left.integer_value, right.integer_value, &result);
        if (!valid) {
            set_error(parser, operator_position);
            return left;
        }
        return make_integer(result, left.start_position);
    }

    {
        double result = operator == '+'
                            ? as_double(left) + as_double(right)
                            : as_double(left) - as_double(right);
        if (!isfinite(result)) {
            set_error(parser, operator_position);
            return left;
        }
        return make_real(result, left.start_position);
    }
}

static Value parse_additive(Parser *parser)
{
    Value left = parse_multiplicative(parser);

    while (!parser->failed) {
        char operator;
        size_t operator_position;
        Value right;

        skip_spaces(parser);
        if (parser->position >= parser->length) {
            break;
        }
        operator = parser->line[parser->position];
        if (operator != '+' && operator != '-') {
            break;
        }

        operator_position = current_position(parser);
        parser->position++;
        right = parse_multiplicative(parser);
        if (parser->failed) {
            break;
        }
        left = apply_additive(parser, left, right, operator, operator_position);
    }

    return left;
}

static bool builder_reserve(StringBuilder *builder, size_t extra)
{
    size_t required;
    size_t new_capacity;
    char *new_data;

    if (extra > SIZE_MAX - builder->length - 1U) {
        return false;
    }
    required = builder->length + extra + 1U;
    if (required <= builder->capacity) {
        return true;
    }

    new_capacity = builder->capacity == 0U ? 128U : builder->capacity;
    while (new_capacity < required) {
        if (new_capacity > SIZE_MAX / 2U) {
            new_capacity = required;
            break;
        }
        new_capacity *= 2U;
    }

    new_data = realloc(builder->data, new_capacity);
    if (new_data == NULL) {
        return false;
    }
    builder->data = new_data;
    builder->capacity = new_capacity;
    return true;
}

static bool builder_append(StringBuilder *builder, const char *text, size_t length)
{
    if (!builder_reserve(builder, length)) {
        return false;
    }
    memcpy(builder->data + builder->length, text, length);
    builder->length += length;
    builder->data[builder->length] = '\0';
    return true;
}

static bool builder_append_value(StringBuilder *builder, Value value)
{
    char formatted[128];
    int count;

    if (value.is_real) {
        /* 15 significant digits match the precision required by the sample outputs. */
        count = snprintf(formatted, sizeof(formatted), "%.15g", value.real_value);
    } else {
        count = snprintf(formatted, sizeof(formatted), "%lld", value.integer_value);
    }
    return count >= 0 && (size_t)count < sizeof(formatted) &&
           builder_append(builder, formatted, (size_t)count) &&
           builder_append(builder, "\n", 1U);
}

static char *evaluate_file_contents(const char *contents, size_t length,
                                    size_t *output_length)
{
    StringBuilder output = { NULL, 0U, 0U };
    size_t line_start = 0U;

    while (line_start < length) {
        size_t line_end = line_start;
        size_t first_non_space;
        Parser parser;
        Value value;

        while (line_end < length && contents[line_end] != '\n') {
            line_end++;
        }

        first_non_space = line_start;
        while (first_non_space < line_end &&
               isspace((unsigned char)contents[first_non_space])) {
            first_non_space++;
        }

        /* Blank lines and full-line comments are skipped, but their bytes still count. */
        if (first_non_space < line_end && contents[first_non_space] != '#') {
            parser.line = contents + line_start;
            parser.length = line_end - line_start;
            parser.position = 0U;
            parser.file_offset = line_start;
            parser.error_position = 0U;
            parser.depth = 0U;
            parser.failed = false;

            value = parse_additive(&parser);
            if (!parser.failed) {
                skip_spaces(&parser);
                if (parser.position < parser.length) {
                    error_at_current(&parser);
                }
            }

            if (parser.failed) {
                char error_text[64];
                int error_count = snprintf(error_text, sizeof(error_text),
                                           "ERROR:%zu\n", parser.error_position);
                free(output.data);
                output.data = NULL;
                output.length = 0U;
                output.capacity = 0U;
                if (error_count < 0 || (size_t)error_count >= sizeof(error_text) ||
                    !builder_append(&output, error_text, (size_t)error_count)) {
                    free(output.data);
                    return NULL;
                }
                *output_length = output.length;
                return output.data;
            }

            if (!builder_append_value(&output, value)) {
                free(output.data);
                return NULL;
            }
        }

        if (line_end < length) {
            line_start = line_end + 1U;
        } else {
            line_start = length;
        }
    }

    if (output.data == NULL) {
        output.data = calloc(1U, 1U);
        if (output.data == NULL) {
            return NULL;
        }
    }
    *output_length = output.length;
    return output.data;
}

static char *read_entire_file(const char *path, size_t *length)
{
    FILE *file = fopen(path, "rb");
    long file_size;
    size_t bytes_read;
    char *buffer;

    if (file == NULL) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return NULL;
    }
    if (fseek(file, 0L, SEEK_END) != 0 || (file_size = ftell(file)) < 0L ||
        fseek(file, 0L, SEEK_SET) != 0) {
        fprintf(stderr, "calc: cannot determine size of '%s'\n", path);
        fclose(file);
        return NULL;
    }
    if ((unsigned long)file_size > (unsigned long)(SIZE_MAX - 1U)) {
        fprintf(stderr, "calc: input file is too large: '%s'\n", path);
        fclose(file);
        return NULL;
    }

    buffer = malloc((size_t)file_size + 1U);
    if (buffer == NULL) {
        fprintf(stderr, "calc: out of memory reading '%s'\n", path);
        fclose(file);
        return NULL;
    }
    bytes_read = fread(buffer, 1U, (size_t)file_size, file);
    if (bytes_read != (size_t)file_size || ferror(file)) {
        fprintf(stderr, "calc: could not read '%s' completely\n", path);
        free(buffer);
        fclose(file);
        return NULL;
    }
    buffer[bytes_read] = '\0';
    fclose(file);
    *length = bytes_read;
    return buffer;
}

static char *copy_path_basename(const char *path)
{
    size_t end = strlen(path);
    size_t start;
    char *copy;

    while (end > 0U && path[end - 1U] == '/') {
        end--;
    }
    start = end;
    while (start > 0U && path[start - 1U] != '/') {
        start--;
    }
    copy = malloc(end - start + 1U);
    if (copy == NULL) {
        return NULL;
    }
    memcpy(copy, path + start, end - start);
    copy[end - start] = '\0';
    return copy;
}

static char *base_without_extension(const char *path)
{
    char *base = copy_path_basename(path);
    size_t length;

    if (base == NULL) {
        return NULL;
    }
    length = strlen(base);
    if (length >= 4U && strcmp(base + length - 4U, ".txt") == 0) {
        base[length - 4U] = '\0';
    }
    return base;
}

static char *make_default_output_dir(const char *input_path, bool is_directory)
{
    const char *base;
    char *temporary_base = NULL;
    int needed;
    char *result;

    if (is_directory) {
        temporary_base = copy_path_basename(input_path);
        if (temporary_base == NULL) {
            return NULL;
        }
        base = temporary_base;
    } else {
        temporary_base = base_without_extension(input_path);
        if (temporary_base == NULL) {
            return NULL;
        }
        base = temporary_base;
    }

    needed = snprintf(NULL, 0, "%s_%s_%s", base,
                      STUDENT_FIRST_NAME, STUDENT_ID);
    if (needed < 0) {
        free(temporary_base);
        return NULL;
    }
    result = malloc((size_t)needed + 1U);
    if (result != NULL) {
        (void)snprintf(result, (size_t)needed + 1U, "%s_%s_%s", base,
                       STUDENT_FIRST_NAME, STUDENT_ID);
    }
    free(temporary_base);
    return result;
}

static char *join_path(const char *directory, const char *filename)
{
    size_t dir_length = strlen(directory);
    size_t file_length = strlen(filename);
    bool needs_slash = dir_length > 0U && directory[dir_length - 1U] != '/';
    char *result;

    if (dir_length > SIZE_MAX - file_length - 2U) {
        return NULL;
    }
    result = malloc(dir_length + (needs_slash ? 1U : 0U) + file_length + 1U);
    if (result == NULL) {
        return NULL;
    }
    (void)snprintf(result, dir_length + (needs_slash ? 1U : 0U) + file_length + 1U,
                   "%s%s%s", directory, needs_slash ? "/" : "", filename);
    return result;
}

static bool ensure_output_directory(const char *path)
{
    struct stat info;

    if (stat(path, &info) == 0) {
        if (S_ISDIR(info.st_mode)) {
            return true;
        }
        fprintf(stderr, "calc: output path '%s' is not a directory\n", path);
        return false;
    }
    if (errno != ENOENT) {
        fprintf(stderr, "calc: cannot inspect output directory '%s': %s\n",
                path, strerror(errno));
        return false;
    }
    if (mkdir(path, 0777) != 0) {
        fprintf(stderr, "calc: cannot create output directory '%s': %s\n",
                path, strerror(errno));
        return false;
    }
    return true;
}

static int process_one_file(const char *input_path, const char *output_dir)
{
    size_t input_length = 0U;
    size_t result_length = 0U;
    char *contents = read_entire_file(input_path, &input_length);
    char *results;
    char *base;
    char *filename;
    char *output_path;
    int needed;
    FILE *output_file;

    if (contents == NULL) {
        return -1;
    }
    results = evaluate_file_contents(contents, input_length, &result_length);
    free(contents);
    if (results == NULL) {
        fprintf(stderr, "calc: out of memory evaluating '%s'\n", input_path);
        return -1;
    }

    base = base_without_extension(input_path);
    if (base == NULL) {
        fprintf(stderr, "calc: out of memory preparing output name\n");
        free(results);
        return -1;
    }

    needed = snprintf(NULL, 0, "%s_%s_%s_%s.txt", base,
                      STUDENT_FIRST_NAME, STUDENT_LAST_NAME, STUDENT_ID);
    if (needed < 0) {
        free(base);
        free(results);
        fprintf(stderr, "calc: could not format output name\n");
        return -1;
    }
    filename = malloc((size_t)needed + 1U);
    if (filename == NULL) {
        free(base);
        free(results);
        fprintf(stderr, "calc: out of memory preparing output name\n");
        return -1;
    }
    (void)snprintf(filename, (size_t)needed + 1U, "%s_%s_%s_%s.txt", base,
                   STUDENT_FIRST_NAME, STUDENT_LAST_NAME, STUDENT_ID);
    free(base);

    output_path = join_path(output_dir, filename);
    free(filename);
    if (output_path == NULL) {
        free(results);
        fprintf(stderr, "calc: out of memory preparing output path\n");
        return -1;
    }

    output_file = fopen(output_path, "wb");
    if (output_file == NULL) {
        fprintf(stderr, "calc: cannot write '%s': %s\n", output_path, strerror(errno));
        free(output_path);
        free(results);
        return -1;
    }
    if (result_length > 0U && fwrite(results, 1U, result_length, output_file) != result_length) {
        fprintf(stderr, "calc: write failed for '%s'\n", output_path);
        fclose(output_file);
        free(output_path);
        free(results);
        return -1;
    }
    if (fclose(output_file) != 0) {
        fprintf(stderr, "calc: could not finish writing '%s'\n", output_path);
        free(output_path);
        free(results);
        return -1;
    }

    free(output_path);
    free(results);
    return 0;
}

static bool has_txt_extension(const char *name)
{
    size_t length = strlen(name);
    return length >= 4U && strcmp(name + length - 4U, ".txt") == 0;
}

static int process_directory(const char *input_dir, const char *requested_output_dir)
{
    struct stat input_info;
    DIR *directory;
    struct dirent *entry;
    char *default_output_dir = NULL;
    const char *output_dir = requested_output_dir;
    int status = 0;

    if (stat(input_dir, &input_info) != 0 || !S_ISDIR(input_info.st_mode)) {
        fprintf(stderr, "calc: input directory '%s' does not exist or is not a directory\n",
                input_dir);
        return -1;
    }
    if (output_dir == NULL) {
        default_output_dir = make_default_output_dir(input_dir, true);
        if (default_output_dir == NULL) {
            fprintf(stderr, "calc: out of memory preparing output directory name\n");
            return -1;
        }
        output_dir = default_output_dir;
    }
    if (!ensure_output_directory(output_dir)) {
        free(default_output_dir);
        return -1;
    }

    directory = opendir(input_dir);
    if (directory == NULL) {
        fprintf(stderr, "calc: cannot open input directory '%s': %s\n",
                input_dir, strerror(errno));
        free(default_output_dir);
        return -1;
    }

    while ((entry = readdir(directory)) != NULL) {
        char *input_path;
        struct stat entry_info;

        if (!has_txt_extension(entry->d_name)) {
            continue;
        }
        input_path = join_path(input_dir, entry->d_name);
        if (input_path == NULL) {
            fprintf(stderr, "calc: out of memory preparing input path\n");
            status = -1;
            break;
        }
        if (stat(input_path, &entry_info) != 0 || !S_ISREG(entry_info.st_mode)) {
            free(input_path);
            continue; /* Only regular .txt files directly inside this directory. */
        }
        if (process_one_file(input_path, output_dir) != 0) {
            status = -1;
            free(input_path);
            break;
        }
        free(input_path);
    }

    if (closedir(directory) != 0 && status == 0) {
        fprintf(stderr, "calc: failed to close input directory '%s'\n", input_dir);
        status = -1;
    }
    free(default_output_dir);
    return status;
}

static void print_usage(FILE *stream)
{
    fprintf(stream,
            "Usage: calc [-o DIR | --output-dir DIR] INPUT.txt\n"
            "       calc [-d DIR | --dir DIR] [-o DIR | --output-dir DIR]\n");
}

int main(int argc, char **argv)
{
    const char *input_file = NULL;
    const char *input_dir = NULL;
    const char *output_dir = NULL;
    char *default_output_dir = NULL;
    int index;
    int result;

    for (index = 1; index < argc; index++) {
        if (strcmp(argv[index], "-o") == 0 ||
            strcmp(argv[index], "--output-dir") == 0) {
            if (index + 1 >= argc) {
                fprintf(stderr, "calc: option '%s' requires a directory\n", argv[index]);
                print_usage(stderr);
                return 2;
            }
            output_dir = argv[++index];
        } else if (strcmp(argv[index], "-d") == 0 ||
                   strcmp(argv[index], "--dir") == 0) {
            if (index + 1 >= argc) {
                fprintf(stderr, "calc: option '%s' requires a directory\n", argv[index]);
                print_usage(stderr);
                return 2;
            }
            input_dir = argv[++index];
        } else if (argv[index][0] == '-') {
            fprintf(stderr, "calc: unknown option '%s'\n", argv[index]);
            print_usage(stderr);
            return 2;
        } else if (input_file == NULL) {
            input_file = argv[index];
        } else {
            fprintf(stderr, "calc: too many input paths\n");
            print_usage(stderr);
            return 2;
        }
    }

    if ((input_dir != NULL && input_file != NULL) ||
        (input_dir == NULL && input_file == NULL)) {
        print_usage(stderr);
        return 2;
    }

    if (input_dir != NULL) {
        result = process_directory(input_dir, output_dir);
        return result == 0 ? 0 : 1;
    }

    if (output_dir == NULL) {
        default_output_dir = make_default_output_dir(input_file, false);
        if (default_output_dir == NULL) {
            fprintf(stderr, "calc: out of memory preparing output directory name\n");
            return 1;
        }
        output_dir = default_output_dir;
    }

    if (!ensure_output_directory(output_dir)) {
        free(default_output_dir);
        return 1;
    }
    result = process_one_file(input_file, output_dir);
    free(default_output_dir);
    return result == 0 ? 0 : 1;
}
