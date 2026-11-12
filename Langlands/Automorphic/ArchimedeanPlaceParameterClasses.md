# Archimedean place parameters of mixed-rank cuspidal classes

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`, at the request of Worker 12 (Task 12). All
declarations lie in the namespace `Langlands.Automorphic`. The module extends the archimedean
place parameters of `Langlands.Automorphic.ArchimedeanPlaceParameter` to the mixed-rank
cuspidal classes `PositiveRankCuspidalClass F = Σ r, CuspidalOperatorRealization.IsoClass F r`,
the constituents of isobaric data. It also records the rank condition built into the
predicates. It constructs no parameter and asserts none exists.

## Declarations

- `OperatorRealization.IsoClass.HasRealPlaceParameter.realRank_eq`: a real place parameter
  `ds` of a class of rank `n` has `realRank ds = n`.
  `OperatorRealization.IsoClass.HasComplexPlaceParameter.length_eq`: a complex place parameter
  has `n` blocks. Both are the first conjunct of the predicate on a representative, by
  induction on the quotient.
- `PositiveRankCuspidalClass.HasRealPlaceParameter c v ds` and
  `PositiveRankCuspidalClass.HasComplexPlaceParameter c v ds`, under
  `[CompactSpace (AdeleQuotient F)]`, are the place parameters of the underlying fixed-rank
  class `c.2` (`CuspidalOperatorRealization.IsoClass.HasRealPlaceParameter` and
  `HasComplexPlaceParameter`).
- `hasRealPlaceParameter_ofFixedRank` and `hasComplexPlaceParameter_ofFixedRank`: for
  `ofFixedRank c` the predicates are those of `c`.
- `PositiveRankCuspidalClass.HasRealPlaceParameter.realRank_eq`: `realRank ds = c.rank`.
  `HasComplexPlaceParameter.length_eq`: `ds.length = c.rank`.

## Source correspondence

The predicates are those of the published `ArchimedeanPlaceParameter`, whose Markdown gives
the source correspondence: Knapp 1994, Theorems 1–2 and 4–5, through Worker 35's
`StandardModule`, and Flath 1979, Theorem 3. This module only transports them to the mixed-rank
index type. That is a derived bookkeeping step with no new source content.

## Scope

Existence of parameters, uniqueness up to permutation of blocks, Galois or arithmetic
transport of parameters (owned by Task 12), and parameters of isobaric data (concatenation over
constituents) are not treated here.
