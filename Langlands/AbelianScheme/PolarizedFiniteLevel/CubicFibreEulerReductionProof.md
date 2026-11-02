# Finite cohomology and the dimension reduction for the actual cubic bundle

`cubicFibreEulerReduction` proves the exact internal proposition
`CubicFibreEulerReductionStatement`. It has no geometric vanishing or Euler-square
assumptions on its unconditional finite-cohomology assertion. The dimension
reduction is conditional exactly as in that proposition.

`Datum.cubicBundle_hasFiniteCohomology` applies the published
`smoothProperLineBundleEulerPolynomial` to `a.canonicalBundle`, the supplied
relative dimension `a.dimension`, and the smooth proper geometrically connected
abelian scheme `a.abelian`. The tensor power `3` is definitionally the actual
`a.cubicBundle`. The theorem obtains finite cohomology from the finite-cohomology
conclusion of the Euler-polynomial theorem; no ampleness input is required.

The general helper
`finrank_eq_of_higherCohomology_isZero_of_eulerSquare` uses the final component of
`eulerCharacteristicBasic` to replace the Euler characteristic by the natural
number dimension of degree-zero cohomology, cast to `ℤ`. Two nonnegative integers
with equal squares are equal. This gives the actual natural-number dimension.

`Datum.cubicBundle_finrank_of_vanishing_of_eulerSquare` rewrites
`6^(2*g) * d^2` as `(6^g*d)^2` and applies that helper. Finally the entry theorem
pairs the unconditional finite-cohomology result with this conditional reduction.
The argument works over an arbitrary field, without positivity restrictions on
`d` or a restriction on the level `n`.

## Provenance and remaining obligations

This proof is an internal specialization and arithmetic composition of the two
published results named above. It does not establish ampleness, the vanishing
hypothesis of the reduction, or the geometric Euler-square equality. Those remain
separate inputs to the final `CubicFibreCohomologyStatement` proof.
