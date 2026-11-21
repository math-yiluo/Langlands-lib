# The Gauss point for arbitrary positive polyradii

This module constructs a `BanachSpectrum` point of the actual
`GeneralizedTateAlgebra r K` for `r : PositivePolyradius (Fin n)` over an
ultrametric normed field `K`. Its value on a series `f` is the existing
weighted Gauss norm of `f`: the supremum of `‖coeff_i(f)‖ · r^i`, with
`r^i` the product of coordinate radii to the powers in the exponent `i`.
No radii are required to belong to the value group. The seminorm agrees
with the norm on scalars and is bounded by the algebra norm with equality.

## Implemented proof

For a nonzero restricted series, the weighted coefficient of some monomial
is positive. The set of exponents whose weighted coefficients are at least
that value is finite by restrictedness; a maximum in this set is a global
maximum. Zero series have every weighted coefficient equal to zero. Given
a monomial order, well-foundedness then gives the first exponent achieving
the norm.

For nonzero `f,g`, let `i,j` be their first maximizing exponents. Any other
pair `(a,b)` with `a+b=i+j` has at least one exponent earlier, since the
monomial order is additive. Its product of weighted coefficients is
strictly smaller than the product at `(i,j)`. Both products involve the
same positive weight `r^(i+j)`, by `PositivePolyradius.weight_add`. Cancel
it to obtain the strict inequality on the actual coefficient products.
Mathlib's `MvPowerSeries.gaussNorm_le_mul` now gives the lower bound for
`‖f*g‖`; the existing normed-ring upper bound gives equality. The zero
cases follow directly, and the construction uses the lexicographic
monomial order for `Fin n`.

`norm_sum_monomial_le_iff` describes the norm of a finite sum of monomials
with pairwise distinct exponents. The coefficient at an exponent in the
list is its supplied coefficient and all other coefficients vanish. Thus
bounding the norm by a nonnegative `B` is equivalent to bounding each
supplied weighted coefficient by `B`.

## Provenance and use

This is an internal extension of the dominant-coefficient argument in
[`TateGaussPoint.lean`](../TateGaussPoint.lean) from the strict unit-radius
algebra to the Library's generalized Tate algebra. It supplies the point
with arbitrary real weights needed to lift an adapted vector norm in the
surjectivity proof for Drinfeld's reduction map. The change of affine
coordinates and the lift to the upper half space are not proved here.
