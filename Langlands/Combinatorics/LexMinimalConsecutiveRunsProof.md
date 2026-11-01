# Consecutive runs in a lexicographically minimal integer word

`Langlands.Combinatorics.lexMinimalConsecutiveRuns` proves exactly the
proposition `Langlands.Combinatorics.LexMinimalConsecutiveRuns`, imported
from the paired statement module. The proof uses the three local closure
hypotheses and lexicographic minimality supplied by that proposition.

The private function `run a m` constructs
`[a,a-1,...,a-(m-1)]` recursively. Auxiliary lemmas compute its length,
identify it with the range-map expression in the statement, split it
after any prescribed number of entries, and bound its entries.
`run_prefix` extracts the maximal initial consecutive run of any nonempty
word. Its length is positive, and if a suffix remains, its first entry
differs from the next expected entry of the run.

The local argument `run_next` shows that, in a lexicographically minimal
word, an entry `x` immediately following a positive run with top `a` and
length `m` must equal `a-m` whenever `x<a`. If `x` is below the last run
entry, the adjacent swap would give a smaller word unless it continues
the run. Equality with the last entry is excluded by the lower-repeat
triple move. In the remaining case, `x` repeats an interior entry of the
run. `commute_left` first moves it past the intervening entries, which
are all at least two smaller. `interior_repeat` then applies the
upper-repeat disjunction. One branch immediately lowers the word; the
other permits a lower-repeat move at the preceding position and also
lowers it. Every operation retains its outside prefix and suffix.

Apply this result to the maximal first run. The noncontinuation
condition forces the first entry of any remaining suffix to be at least
`a`. Strong induction on word length now handles that suffix using the
predicate `Q v := P (run a m ++ v)`. All three local closures pass to
`Q`, and minimality passes to it by prefixing a strict lexicographic
comparison with the fixed run. Positivity of the removed length makes
the induction decrease. The suffix decomposition and the comparison of
its first entry with `a` give the required adjacent chain on run tops.
Concatenation gives the original word. Finally, the range-map lemma
converts the recursive runs into the exact expression of the statement.
The empty word uses the empty list of runs.

This is a derived finite combinatorial proof following the argument
isolated in the statement's provenance discussion of Jantzen (2000),
Lemma 2.2.2, printed pp.545-547 / PDF pp.7-9, registered as
`jantzen-2000-square-integrable-classical-i`. The recursion and strong
induction implement that argument without further representation
theory. The statement module records the corrected direction of the
source's first lexicographic comparison and the terminal case.

The theorem assumes actual membership, minimality, and all three local
closures of the arbitrary word predicate. It proves neither the
existence of a least word for an arbitrary family nor any Jacquet
closure property. It supplies no segment extraction, analytic
inequality, strong segment-head assertion, or representation
classification.
