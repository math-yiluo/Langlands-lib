# Positive-depth rank-one exchange over the maximal unramified field

This internal proof module adapts `MoyPrasadRankOne` and
`MoyPrasadDoubleRefinement` to the actual maximal-unramified building data.
The commutator predicate and ordinary rank-one proof are reused from
Worker 359’s Task 6191 revision-10 draft, with coauthorship.
`LocalTorusCommutatorFriendly` is exactly the explicit first clause of S1
that is the sole extra premise in `LocalMoyPrasadPositiveProductStatement`.
It does not include any other clause of S1 or any part of S2.

For two root-filtration elements in opposite directions at depths `r,s ≥ 0`
with positive sum, the proof uses the field-independent actual rank-one
factorization. It retains both root depths. The middle coordinate is lifted
to the represented centralizer. Rewriting the original commutator using
these coordinates and applying the explicit premise places that coordinate
in the original torus filtration at the sum of the actual input valuations,
then antitonicity lowers it to `r+s`. Identity inputs are handled directly.
The set-product lemma states the corresponding literal inclusion.

For a doubled positive root input at depth `r`, V4 places it in the ordinary
root subgroup at depth `r/2`. The integer-valued higher-depth difference
lemma places the difference of the positive coordinate and the original
input at ordinary-root depth `r`. Thus the output stays in the original
ordinary/doubled block, and its torus coordinate has depth `r/2+s`.
`exists_order_eq_one F` supplies the integer root-system geometry used in
that refinement. The proof never gives the maximal unramified extension a
nonarchimedean local-field instance.
