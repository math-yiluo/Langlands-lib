# Lifting a vector norm to Drinfeld's upper half space

For a proper nontrivially normed field `F`, a complete ultrametric
nontrivially normed field `K` with `NormedAlgebra F K`, and `d ≥ 1`,
`pointOfVectorNorm K ν` chooses a point of `Omega F K d` reducing to the
class of `ν : VectorNorm F (Fin (d + 1) → F)`. This yields
`reduction_surjective` for the published reduction map. The construction
is by choice for each representative norm and does not claim continuity,
compatibility of choices under homothety, or equivariance of the lift.

## The diagonal Gauss point

For positive weights `r₁,…,r_d`, choose a polydisc in the Library's affine
chart system with radius bounding all the weights. The bounded
coefficient-preserving restriction descends from its presentation with
zero relation ideal to the actual generalized Tate algebra of polyradius
`r`. Pull back the [weighted Gauss point](GeneralizedTateAlgebra/GaussPoint.lean)
along that map and use the chosen chart to view it in the affine space.
The original affine coordinate functions restrict to the coordinate
series at `r`, with constants unchanged. The values of an affine-linear
form with coefficient vector `a` over `F` are therefore

`max(‖a₀‖, max_{i>0} ‖aᵢ‖ · rᵢ)`.

Lean uses the equivalent criterion for a nonnegative upper bound: the
constant and coordinate monomials have distinct exponents, and
`norm_sum_monomial_le_iff` bounds the norm by bounding each weighted term.
The scalar norms over `F` are unchanged by `algebraMap F K`. In particular
if the value is zero, every coefficient is zero, so this point lies in
`Omega`.

## Change of basis and the reduction

Choose a basis `b` adapted to `ν` using
[`DrinfeldAdaptedBasis.lean`](DrinfeldAdaptedBasis.lean) and take
`rᵢ = ν(bᵢ)/ν(b₀)` for `i>0`. The weight 1 of the constant monomial
is `ν(b₀)/ν(b₀)`. The coordinate matrix, with the transpose for row
vectors, takes `a` to `b.repr a`. Apply the published `actionMap` of this
matrix to the diagonal Gauss point. By equivariance of reduction, the
new norm on `a` has the Gauss value on `b.repr a`. The characterization
of adaptedness now identifies that value with `ν(a)/ν(b₀)`. This is a
positive global rescaling, so the reduction class is exactly `[ν]`.

## Source and derived choices

Rémy–Thuillier–Werner, *Bruhat-Tits buildings and analytic geometry*
(arXiv:1110.1362, 2012), §2.1.3, p. 18, registered as
`remy-thuillier-werner-2012-bruhat-tits-analytic-geometry`, SHA-256
`f176a2657963c2e6da49a2e0282353097fff8ad67b7cf17f51c2372325591d0b`.
The source obtains a section of reduction by extending an adapted norm
as a Gauss norm on the symmetric algebra. The implementation constructs
weighted Gauss points on the Library's actual affine charts over `K`,
then uses the change of basis action. The extension of scalars and the
affine normalization preserve the induced class on the `F`-linear forms;
no global section properties from the source are asserted here.
