#ifdef Assert
#undef Assert
#include <stdio.h>
#define Assert(x, msg) { if (!(x)) { printf("Assertion: %s: %s %d: %s\n", msg, __FILE__, __LINE__, #x); exit(1); } }
#endif
#include <stdint.h>
#if (defined(__GNUC__) && (__GNUC__ >= 3)) || defined(__INTEL_COMPILER) || defined(__Clang__)
#  ifndef likely
#    define likely(x)      __builtin_expect(!!(x), 1)
#  endif
#  ifndef unlikely
#    define unlikely(x)    __builtin_expect(!!(x), 0)
#  endif
#else
#  ifndef likely
#    define likely(x)      x
#  endif
#  ifndef unlikely
#    define unlikely(x)    x
#  endif
#endif

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    #define get_matched_bits __builtin_ctzl
#else
    #define get_matched_bits __builtin_clzl
#endif

static inline int get_match_len(const unsigned char *a, const unsigned char *b, long max)
{
    register unsigned long len = 0;
    register unsigned long xor = 0;
    register int check_loops = max/sizeof(unsigned long);
    while(check_loops-- > 0) {
        xor = (*(unsigned long *)(a+len)) ^ (*(unsigned long *)(b+len));
        if (xor) break;
        len += sizeof(unsigned long);
    }
    if (unlikely(0 == xor)) {
        while (len < max) {
            if (a[len] != b[len]) break;
            len++;
        }
        return len;
    }
    xor = get_matched_bits(xor)>>3;
    return (int)(len + xor);
}

local uInt longest_match(s, cur_match)
    deflate_state *s;
    IPos cur_match;                             /* current match */
{
    unsigned chain_length = s->max_chain_length;/* max hash chain length */
    register Bytef *scan = s->window + s->strstart; /* current string */
    register Bytef *match;                      /* matched string */
    register int len;                           /* length of current match */
    int best_len = (int)s->prev_length;         /* best match length so far */
    int nice_match = s->nice_match;             /* stop if match long enough */
    IPos limit = s->strstart > (IPos)MAX_DIST(s) ?
        s->strstart - (IPos)MAX_DIST(s) : NIL;
    Bytef *match_head = s->window;
    /* Stop when cur_match becomes <= limit. To simplify the code,
     * we prevent matches with the string of window index 0.
     */
    Posf *prev = s->prev;
    uInt wmask = s->w_mask;

    /* The code is optimized for HASH_BITS >= 8 and MAX_MATCH-2 multiple of 16.
     * It is easy to get rid of this optimization if necessary.
     */
    Assert(s->hash_bits >= 8 && MAX_MATCH == 258, "Code too clever");

    /* Do not waste too much time if we already have a good match: */
    if (s->prev_length >= s->good_match) {
        chain_length >>= 2;
    }
    /* Do not look for matches beyond the end of the input. This is necessary
     * to make deflate deterministic.
     */
    if ((uInt)nice_match > s->lookahead) nice_match = (int)s->lookahead;

    Assert((ulg)s->strstart <= s->window_size-MIN_LOOKAHEAD, "need lookahead");

    /*
     * This implementation is based on algorithm and code described at:
     * http://www.gildor.org/en/projects/zlib
     * with some minor changes/tunes for 32bits/64bits platforms.
     * It uses the hash chain indexed by the "farthest" hash code to
     * reduce number of check loops for "lazy_match".
     * This also eliminates those unnecessary check loops in legacy
     * longest_match's do..while loop if the "farthest code" is out
     * of search buffer
     *
    */
    int offset = 0;
    if (best_len > MIN_MATCH) {
        /* search for most distant hash code */
        register int i;
        register ush hash = 0;
        register IPos pos;

        UPDATE_HASH(s, hash, scan[1]);
        UPDATE_HASH(s, hash, scan[2]);
        for (i = 3; i <= best_len; i++) {
            UPDATE_HASH(s, hash, scan[i]);
            pos = s->head[hash];
            if (pos < cur_match) {
                offset = i - 2;
                cur_match = pos;
            }
        }

        /* update variables to correspond offset */
        limit += offset;
        if (cur_match < limit) return best_len;

        match_head -= offset;
    }

    do {
        Assert(cur_match < s->strstart, "no future");
        match = match_head + cur_match;

        /* Skip to next match if the match length cannot increase
         * or if the match length is less than 2.  Note that the checks below
         * for insufficient lookahead only occur occasionally for performance
         * reasons.  Therefore uninitialized memory will be accessed, and
         * conditional jumps will be made that depend on those values.
         * However the length of the match is limited to the lookahead, so
         * the output of deflate is not affected by the uninitialized values.
         */
        /* This code assumes sizeof(unsigned short) == 2. Do not use
         * UNALIGNED_OK if your compiler uses a different size.
         */
        unsigned char *win = match_head;
        int cont = 1;

        /* following code is based on Cloudflare's improvements.
         * The improvements do:
         *  1. ease the compiler to yield good code layout
         *     to improving instruction-fetching efficiency
         *  2. examines sizeof(machine-width)-byte-match at a time
         *     unsigned long is 4 bytes on 32bits platform, 8 bytes
         *     on 64bits platform
         *  3. use clz/ctz instructions on modern processors
         * While new change is to compare based on different best_len
		 * so registers are fully used and get higher prossiblity to
         * find longer match for later get_match_len
         */
        if (best_len < sizeof(unsigned long)) {
            /* just load one chunk into register */
            unsigned long scan_chunk = *(unsigned long *)scan;
            unsigned long read_chunk;
            short len = 0;
            do {
                match = win + cur_match;
                read_chunk = *(unsigned long *)match;
                len = get_matched_bits(read_chunk ^ scan_chunk)>>3;
                if (len <= best_len) {
                    /* move to next elem on current chain */
                    cur_match = prev[cur_match & wmask];
                    if (cur_match > limit && --chain_length != 0) continue;
                    else cont = 0;
                }
                break;
            } while(1);
        } else {
            /* more than register width, load HEAD and END */
            unsigned long scan_head = *(unsigned long *)scan;
            unsigned long scan_end = *(unsigned long *)(scan+best_len-sizeof(unsigned long)+1);
            unsigned long read_head, read_end;
            do {
                match = win + cur_match;
                read_head = *(unsigned long *)match;
                read_end = *(unsigned long *)(match+best_len-sizeof(unsigned long)+1);
                if ((read_head!=scan_head) || (read_end !=scan_end)) {
                    /* move to next elem on current chain */
                    cur_match = prev[cur_match & wmask];
                    if (cur_match > limit && --chain_length != 0) continue;
                    else cont = 0;
                }
                break;
            } while(1);
        }

        if (!cont)
            break;

        /* search for macthed length */
        len = get_match_len(match, scan, MAX_MATCH);

        if (len > best_len) {
            /* found longer string */
            s->match_start = cur_match - offset;
            best_len = len;
            /* good enough? */
            if (len >= nice_match) break;
            /* following code block is from
             * http://www.gildor.org/en/projects/zlib
             */
            if (s->level > 4 && len >= MIN_MATCH && (cur_match - offset + len < s->strstart)) {
                IPos pos, distant;
                register int i;
                register ush hash = 0;
                register int check_len = len - MIN_MATCH + 1;

                /* go back to offset 0 */
                cur_match -= offset; limit -= offset;
                offset = 0;
                distant = cur_match;

                for (i = 0; i <check_len; i++) {
                    pos = prev[(cur_match + i) & wmask];
                    if (pos < distant) {
                        /* this hash chain is more distant, use it */
                        distant = pos;
                        offset = i;
                    }
                }
                if (distant < limit + offset) break;

                /* Try hash head at len-(MIN_MATCH-1) position to see if we could get
                 * a better cur_match at the end of string. Using (MIN_MATCH-1) lets
                 * us to include one more byte into hash - the byte which will be checked
                 * in main loop now, and which allows to grow match by 1.
                 */
                UPDATE_HASH(s, hash, scan[check_len]);
                UPDATE_HASH(s, hash, scan[check_len+1]);
                UPDATE_HASH(s, hash, scan[check_len+2]);
                pos = s->head[hash];
                if (pos < distant) {
                    offset = check_len;
                    distant = pos;
                }
                if (distant < limit + offset) break;

                /* update offset-dependent vars */
                limit += offset;
                match_head = s->window - offset;
                cur_match = distant;
                continue;
            }
        }
		cur_match = prev[cur_match & wmask];
    } while (cur_match > limit && --chain_length != 0);

	return ((uInt)best_len <= s->lookahead)? best_len : s->lookahead;
}
