# Continuity of the relative Laurent Gauss section

Let `K : Type u` be a complete ultrametric normed field, let `A` be an actual
`PresentedAffinoidAlgebra K`, and let `t` be a positive real number.
`RelativeLaurentAnnulus.gaussSection` is a continuous map

`M(A) → M(RelativeLaurentAnnulus.algebra K A t)`.

Its value is the actual completed-residue-field Gauss point `sectionPoint`
constructed in `RelativeLaurentGaussSection`. The theorem
`restriction_gaussSection` proves that its composite with restriction along the
actual structural map `baseMap` is the identity on `M(A)`.

The target is the existing enlarged weighted Tate presentation: it retains the
old defining ideal and adjoins two variables of radii `t` and `t⁻¹`, imposing their
product to be one, with the closed generated ideal used for the quotient. This
module proves continuity of that specific section. There is no independence
assumption on the radius, no strictness assumption on the presentation, and no
nontrivial-valuation, reducedness, or nonzero hypothesis. The original coordinate
tuple may be empty. Empty spectra are allowed. Every construction remains at
universe `u`.

## Finite Laurent expressions and density

The equation in the actual quotient proves `coordinate_mul`, from which
`coordinateUnit` packages the newly adjoined variable and its inverse as a unit.
`polynomialMap` is the genuine ring homomorphism from `AddMonoidAlgebra A ℤ` to
the quotient obtained by sending a coefficient to `baseMap` and an integer
exponent to the corresponding power of this unit. Thus a single term of exponent
`n` and coefficient `a` maps to `baseMap a * coordinateUnit^n`.

`baseMap_mem_polynomialMap_range` puts the whole coefficient algebra in the
range. `coordinate_mem_polynomialMap_range` includes every scalar presentation
coordinate: the old ones are images of coordinates of `A`, and the two new ones
are the Laurent monomials with exponents `1` and `-1`. Induction on scalar
multivariate polynomials then proves `presentation_polynomial_mem_range`.
The published `GeneralizedTateAlgebra.denseRange_polynomialMap`, composed with
the continuous surjective presentation map, gives a dense subset of the
quotient contained in this range. Consequently `denseRange_polynomialMap`
proves density of finite Laurent expressions in the actual quotient norm.
These density constructions do not require completeness of `K`.

## Evaluation and the finite norm formula

For a point `x` of `M(A)`, `residuePolynomial` applies the actual completed
residue map `A → H(x)` coefficientwise. Its target is the existing
`GaussLaurent H(x) t`, and its coefficient at `n` is the residue image of the
coefficient of the original polynomial at `n`.

`evaluation_coordinateUnit` identifies the evaluated quotient unit with the
actual Laurent variable unit in the residue-field completion. Mapping units
commutes with integer powers. Induction on finite Laurent expressions, together
with the existing coefficient evaluation identity, therefore proves
`evaluation_polynomialMap`: evaluation in the fiber is exactly the completion
image of `residuePolynomial`.

The norm of the completed residue image of `a` is `x(a)`. Using the coefficient
bounds and the definition of the Laurent Gauss norm,
`sectionPoint_polynomialMap` consequently identifies the value on a finite
Laurent expression with the finite supremum of

`Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n`

in `NNReal`, coerced to `ℝ`, over the fixed support of `p.coeff`. The weight is
the positive integer-power weight `t^n`. This support belongs to the original
polynomial and is independent of `x`; vanishing residue coefficients cause no
problem. An empty support has supremum zero. Continuity of the individual
spectrum evaluations, multiplication by a fixed weight, and finite supremum
then proves `continuous_sectionPoint_polynomialMap`.

## Passage to all quotient elements

`sectionPoint_dist_le` applies the published
`BanachSpectrum.abs_sub_le_norm_sub` to the actual spectrum point above `x`.
It bounds the distance between the section's values on `b` and `c` by the norm
distance between `b` and `c`, uniformly for every base point `x`.

For `continuous_sectionPoint_apply`, fix an element `b`, a base point, and a
positive tolerance. Density supplies a finite Laurent expression within one
third of that tolerance of `b`. Its evaluation is continuous at the chosen base
point. The uniform estimate controls the two approximation errors, and the
triangle inequality combines them with the finite expression's continuity
error. This proves continuity of evaluation on every actual quotient element.
The induced pointwise topology on `BanachSpectrum` then proves
`continuous_sectionPoint`, which supplies the continuity field of `gaussSection`.
The identity under restriction follows from the existing
`restriction_sectionPoint` identity.

## Provenance and scope

This is an internal construction derived from the actual relative annulus,
completed residue maps, all-radius Laurent Gauss norm, scalar polynomial
density, and spectrum evaluation estimate already imported by Lean name. It
claims no numbered result from external literature. The Markdown describes the
implemented finite-polynomial approximation proof.

The continuous section is a supporting construction for generalized affinoid
geometry. It does not construct domain scalar base change, strictify arbitrary
presentations, decompose pullbacks into ambient rational pieces, or prove
`Domain.FiniteRationalCoverStatement`.
