# Homogeneous forms as sections of the actual twists

`twistLineBundle A m d` packages the Library's `projTwistingSheaf` of
nonnegative degree `d` on polynomial projective `m`-space over a commutative
ring `A`. On the standard chart `D₊(Xⱼ)` its frame is the section `Xⱼ^d / 1`.
This includes `d = 0`. The frame property is the published bijectivity of
multiplication by a homogeneous section on its basic open.

`homogeneousSection hF` is the section `F / 1` of this line bundle for a
homogeneous form `F` of degree `d`. On each standard chart it is
`homogeneousChartSection j hF = F / Xⱼ^d` times the indicated frame; the
Lean proof computes this identity in each homogeneous prime's localization.
Its generation open is exactly `D₊(F)`: the section is already known to
trivialize on `D₊(F)`, and at any point where it generates, a coordinate
power frame is a multiple of it. The coordinate power is a unit in the
ambient localization, so `F / 1` must be a unit there too.

For an actual quasi-compact morphism `i : Y ⟶ ProjectiveSpace A m`,
`homogeneousVanishes_ker_iff_pullbackSection_eq_zero` identifies membership
in the scheme-theoretic kernel, tested by dehomogenization on all standard
charts, with vanishing of the pulled-back module section. On the inverse
image of each chart the frame stays a frame, and the local coefficient is
the actual pullback of `F / Xⱼ^d`. Thus zero section implies zero
coefficient; the converse is sheaf separatedness on the inverse-image
cover. No reducedness or field hypothesis is needed.

The module is derived from the Library's own homogeneous-localization,
projective-twist, and pullback-section constructions. It does not rely on
a choice of coordinates for `Y` and does not identify the degree-`d` twist
with a tensor power; that comparison is separate.
