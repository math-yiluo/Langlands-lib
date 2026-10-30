# Proof of the graded factor repetition criterion

Module `Langlands.Representation.Filtration.GradedRepetitionProof`.

`Langlands.gradedFactorRepetitionCriterion.{uK,uG,uY}` proves
`Langlands.GradedFactorRepetitionCriterion` without additional hypotheses.
The directly usable theorem is
`Langlands.ObjectRepFiltration.exists_equiv_factors_of_equiv_graded`.
The three universes of the field, acting monoid, and carrier remain
independent.

Worker 257 proposed the abstract interface and the additive multiplicity route;
Worker 122 implemented this proof. This is an internal derivation from the
Library's generic actual-series results, rather than a transcription of a
literature theorem.

Let `t` be the supplied composition series of `Y`, and let `u` be the
arbitrary finite filtration. The proof proceeds as follows.

1. The finite length `N` of `Y` bounds the length of each graded piece of `u`,
   by `repLength_eq_sum_of_filtration`. Thus the piece at `i` has an actual
   composition series `r`. Its carrier is nontrivial, so `r` has positive
   length.
2. Choose the first simple factor `τ` of `r`. Its multiplicity in `r` is
   positive because that first factor is equivalent to itself.
3. `jordanHolderFiltrationDecomposition` supplies composition series and
   counts for every piece of `u`; their counts for `τ` sum to the count in
   `t`. Uniqueness of multiplicity identifies the count at `i` with the
   positive count in `r`. Transport along the given equivalence of pieces,
   followed by uniqueness, makes the count at `j` equal to it.
4. The distinct positions `i` and `j` therefore contribute at least two to
   the ambient count. If `t` had no distinct equivalent factors, its subtype
   of positions equivalent to `τ` would be subsingleton, so that same count
   would be at most one. This contradiction gives the two required indices.

This proof uses arbitrary invariant filtrations and actual composition series;
it does not split extensions. In particular, the pieces of `u` need not be
simple, and pieces other than the specified nonzero one may vanish.

The direct imports are the statement and
`Langlands.Representation.Filtration.MultiplicityAdditivityProof`.
The latter supplies generic module length, actual-series refinement,
Jordan–Hölder independence, and transport. This helper has no p-adic, Jacquet,
segment, special-head, tempered, or other GL classification dependency.
It establishes only the generic repetition implication; construction of the
filtrations used in the distinct supercuspidal product theorem remains separate.
