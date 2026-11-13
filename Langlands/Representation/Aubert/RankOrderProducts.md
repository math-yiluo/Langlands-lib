# Additivity and cancellation for rank order

Helper module for the proof of
`Langlands.Aubert.SocleProductLeadingTermStatement`. Worker 104 and Worker
597 wrote it in an earlier project instance.

These internal combinatorial lemmas follow directly from the published
definition of `Multisegment.RankLE` in `Aubert/MultisegmentRankOrder`:
`RankLE a' a` means that `a'` and `a` have equal cuspidal content and, for
every segment `I`, `containmentCount I a ≤ containmentCount I a'`. The proofs use
`cuspidalContent_add` and `containmentCount_add`, which say that cuspidal
content and each containment count are additive under multiset addition.

- `RankLE.add`: if `RankLE a' a` and `RankLE b' b`, then
  `RankLE (a' + b') (a + b)`. Add the content equalities and the count
  inequalities.
- `rankLE_add_right_iff`: `RankLE (a + c) (b + c) ↔ RankLE a b`. Cancel the
  common summand in the content equality and in each count inequality. The
  converse direction is `RankLE.add` with reflexivity.
- `RankLE.eq_of_add_eq`: if `RankLE a' a`, `RankLE b' b` and
  `a' + b' = a + b`, then `a' = a` and `b' = b`. Equality of the summed counts
  and the count inequality for `b` give
  `containmentCount I a' ≤ containmentCount I a` for every `I`, that is,
  `RankLE a a'`. Antisymmetry then gives `a' = a`, and additive cancellation
  gives `b' = b`.

The main proof uses only `RankLE.add`. The other two lemmas are general
consequences of the same additivity, kept for reuse.

## Provenance

These are derived internal lemmas about the published Library order; they are
not taken from a literature source.
