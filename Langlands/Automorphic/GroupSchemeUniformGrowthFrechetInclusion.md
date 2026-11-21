# Increasing the growth exponent and decreasing the level

This module constructs the continuous linear inclusion between the Library's
spaces of functions of uniform moderate growth. It is internal infrastructure
for the fixed-level argument in Bernstein–Lapid §7.6, in particular the
passage to all sufficiently large exponents described in
`Langlands/Global/AdelicLocalFinitenessStatement.md`. The construction works
directly with the Library's matrix source norm, not with a Siegel-domain weight.

## Map and scope

In `Langlands.Automorphic.GroupSchemeFunctions`, let `F` be a number field,
`G` an affine group scheme over `F`, and fix the smooth atlas and differential
calculus data of `UniformGrowthFrechetSpace`. Fix also the closed matrix
embedding `rho` of size `N > 0`. Write `𝔉^R_L` for the space
`UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`.

For real exponents `R ≤ S` and subgroups `J ≤ L` of `G(𝔸_f)`,
`UniformGrowthFrechetSpace.inclusion` is a continuous complex-linear map
`𝔉^R_L → 𝔉^S_J`. It preserves the underlying function
(`UniformGrowthFrechetSpace.toFun_inclusion`) and is injective
(`UniformGrowthFrechetSpace.inclusion_injective`). No openness or compactness
of either subgroup is needed. The module does not assert completeness or
closedness of the image, or prove local finiteness.

## Construction

Let `H(x) = RepresentationGrowth.adelicSourceNorm F G rho x`. The Library
relates its normalized height to this norm by `adelicHeight(x) = K H(x)`,
where `K = N^(∑_{v | ∞} mult(v)) > 0`, and proves `adelicHeight(x) ≥ 1`.
Thus `H(x) ≥ K⁻¹` at every adelic point, and `H(x)^(R − S) ≤ K^(S − R)`.
Multiplying a derivative bound by this constant shows
`HasUniformGrowthExponent.mono`: if `B` bounds a derivative after weighting by
`H^(-R)`, then `max(B, 0) K^(S − R)` bounds it after weighting by `H^(-S)`.
Right `L`-invariance implies right `J`-invariance. These two facts give a
submodule inclusion, hence give the identity on the underlying functions and
its injectivity.

In the target topology one tests continuity after each weighted derivative to
`ℓ^∞(G(𝔸))`. For each enveloping algebra element the target weighted derivative
of an included function is the source weighted derivative multiplied pointwise
by `H^(R − S)`, as an element of `ℓ^∞`. This multiplier belongs to `ℓ^∞` by the
same bound. Each source weighted derivative is continuous and multiplication
by a fixed element of `ℓ^∞` is continuous. The target's defining infimum of
induced topologies now gives the continuity of the inclusion.
