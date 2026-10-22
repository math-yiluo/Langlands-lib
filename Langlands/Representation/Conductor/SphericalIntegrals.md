# Corank-one integrals of spherical tests

The coefficient field is the complex numbers. The matrix field `F` carries
the supplied valuation and topology; no local-field hypothesis is needed,
because nothing here is analytic beyond the definitions of the integral and
its convergence. The two representation carriers have independent universes,
and no topology is placed on either of them. The smaller positive rank is
`n + 1` and the larger rank is `(n + 1) + 1`, so a rank-one spherical test
against a rank-two representation is included.

## The test as a second JPSS member

The representation `σ` of `GL_(n+1)(F)` and the functional
`ℓ' ∈ glInverseFunctionals ψ n σ` are explicit. Here `ψ` is the supplied unitary
additive character, and the functional is equivariant for the published
inverse standard character `u ↦ ψ(Σ_i u_(i,i+1))^(-1)` of the actual upper
unitriangular group. This is the source's model `W(σ, ψ̄)`, because `ψ` is
unitary. A normalized spherical test `w' : SphericalTest σ ℓ'` is the
published notion of `Langlands.Representation.Conductor.SphericalTests`: a
right `GL_(n+1)(O_F)`-invariant vector of the coefficient image with value one
at the identity.

`sphericalTestWhittaker ψ w'` is the same function viewed as an element of the
published space `InverseWhittakerFunctions ψ n` of inverse-character
equivariant functions. Here `InverseWhittakerFunctions ψ n` is the type of the
second argument of the published corank-one integral. The coercion forgets the
coefficient-image membership and the spherical normalization, and
`sphericalTestWhittaker_apply` proves that its values are the values of
`sphericalTestFunction σ ℓ' w'`.

## Integral invariance of the integrand

The absolute value `abv : AbsoluteValue F ℝ` is explicit. The two results
below assume

`habv : ∀ x, v(x) = 1 → abv x = 1`,

where `v` is the supplied valuation `ValuativeRel.valuation F`. The normalized
absolute value of a nonarchimedean local field satisfies `habv`. The module
does not tie `abv` to the valuation in any other way.

`valuation_det_of_mem_integralSubgroup` proves that the determinant of every
element of the published integral subgroup `integralSubgroup O_F n` (the image
of `GL_(n+1)(O_F)`) has valuation one. The determinant of an integral
representative is a unit of the valuation integers, and the determinant
commutes with the coefficient map. Consequently
`determinantWeight_mul_integral` proves `|det(g k)|^s = |det g|^s` for such `k`
and every complex `s`, where `|det g|^s` is the published
`determinantWeight abv g s`.

The representation `π` of `GL_((n+1)+1)(F)` and the functional
`ell ∈ glFunctionals ψ (n + 1) π` for the standard character are explicit. For
a vector `w` of the coefficient image that satisfies the published
restriction-invariance clause `IsIntegralInvariantOnRestriction π ell w`
(Jacquet's uniqueness condition after Theorem 1),
`corankOneFunction_sphericalTest_mul_integral` proves that the published
corank-one function

`g ↦ W(diag(g, 1)) W'(g) |det g|^(s - 1/2)`,

with `W = w` and `W' = sphericalTestWhittaker ψ w'`, is right invariant under
the integral group. The three factors are invariant separately: the first by
the restriction clause, the second by the right invariance of a spherical
test, and the third by `determinantWeight_mul_integral`. Together with the
Iwasawa decomposition, this invariance reduces the source's integrals to sums
over the diagonal torus; neither the decomposition nor that reduction is
proved here.

## The test integral

The quotient `LeftUnipotentQuotient n F` is the actual left coset space
`N_(n+1) \ GL_(n+1)(F)`. Its measurable structure and the measure
`μ : Measure (LeftUnipotentQuotient n F)` are explicit; neither a Haar
normalization nor compatibility with Haar measures on `GL_(n+1)(F)` and
`N_(n+1)` is assumed.

`sphericalTestIntegral ψ abv μ π ell w w' s` is the published coefficient-model
integral `corankOneModelIntegral` with `w'` as the second vector. That is,

`Ψ(s; W, W') = ∫_(N_(n+1) \ GL_(n+1)) W(diag(g, 1)) W'(g) |det g|^(s - 1/2) dμ(g)`,

and `sphericalTestIntegral_eq` records this definitionally as the Bochner
integral of the published descended integrand `corankOneIntegrand`.
The integrand is well defined on the quotient: on the embedded unipotent
group the larger standard character restricts to the smaller one, which
cancels against its inverse. The published `corankOneFunction_invariant`
proves this. Lean's Bochner integral is zero
for a non-integrable integrand. So the value is meaningful only together with
the convergence predicate.

`SphericalTestConverges ψ abv μ π ell w w' s` is integrability of the same
descended integrand with respect to `μ` (the published `CorankOneConverges`),
that is, absolute convergence of the integral. It is not mere existence of
Lean's total integral. `SphericalTestConvergesOnRight ψ abv μ π ell w w'`
asserts convergence for all `s` with `Re s > c`, for some real `c` that may
depend on the pair of vectors.

None of these definitions asserts convergence, rational continuation, a
relation to an L-factor, Jacquet's essential-vector identity
`Ψ(s; W, W(·; x; ψ̄)) = ∏_i P(q^(-s) x_i)^(-1)`, or the existence of any
spherical test or restriction-invariant vector.

## Provenance and scope

Hervé Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific Journal of Mathematics 260 (2012), 515–525,
DOI 10.2140/pjm.2012.260.515.

- Literature ID: `jacquet-2012-conductor-correction`.
- SHA-256: `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
- Retained PDF:
  `/home/taskhub/central-library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`.

The additive character of conductor `O_F`, the measure normalizations (volume
one for `G_r(O_F)` and `N_r(O_F)`) and the characters `θ_(r,ψ)` are on pages
515–516. Theorem 1 is on page 517: it pairs `W ∈ W(π, ψ)` on `G_r` with the
spherical function `W(g; x; ψ̄)` on `G_(r-1)` through the integral over
`N_(r-1) \ G_(r-1)` of `W(diag(g, 1)) W(g; x; ψ̄) |det g|^(s - 1/2)`. The
restriction-invariance clause follows it on the same page. The integral
`Ψ(s, W, W')` with the same exponent appears again on page 519. These pages
were read directly.

This pair is a derived preparation for Theorem 1. With `r = (n + 1) + 1`, the
integral is the source's integral with `W` in the larger standard-character
model and a normalized level-zero test of an inverse-character model in place
of the spectrally indexed spherical function. The measure, the absolute value
and the additive character are inputs, so the source's normalizations
(conductor of `ψ`, unit volumes) are not imposed here. The spectrally indexed
spherical functions, their Satake parametrization, the normalized measure, the
conductor condition on `ψ` and the standard L-polynomial `P` must still be
supplied before Theorem 1's identity can be stated for these integrals. The
two invariance results are internal algebraic bridges. The integral
definitions are specializations of Worker 31's published corank-one JPSS
integrals and add no new analytic content.

## Dependencies

Imports are the published modules
`Langlands.Representation.Conductor.SphericalTests` and
`Langlands.Representation.RankinSelberg.QuotientIntegrals` (with its imports,
including `Langlands.Representation.Whittaker.GeneralLinear`), present in
Library commit `22b4f024e0d4218752e970d09329d1799f6d81d1`. Environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Worker 43 authored this module;
the corank-one integral, its integrand, convergence predicate and the
coefficient-model specialization are Worker 31's published definitions.
