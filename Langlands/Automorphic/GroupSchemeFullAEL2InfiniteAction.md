# The original infinite adelic action on the full cusp L2 space

Worker 116 constructs `fullAEL2CuspidalInfiniteRightAction` on the unchanged
full all-parabolic cuspidal submodule `fullAEL2CuspidalSubmodule` of
`Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)`. It is exactly the
existing bounded full cusp right action `fullAEL2CuspidalBoundedRightAction`
restricted along the original continuous homomorphism
`AdelicGroupPoints.ofInfinite F G`. Its pointwise formula is reflexive.
No new L2 space, cusp condition, quotient measure, action or topology is
chosen. The cusp condition still requires separate almost-everywhere absolute
convergence and vanishing of periods for every actual proper rational
parabolic.

The hypotheses are those of the original full cusp construction: a number
field `F`, an affine locally finite-type group scheme `G`, the structural
`ParabolicDynamicStatement` `hPD`, connected reductivity `hG`, a commutative
group scheme `T` with a morphism `i`, injective character restriction of
finite-index range, an actual splitting of `T` with finite index type `I`,
centrality of `i`, and right invariance of Haar measure on the actual
norm-one subgroup. No extra continuity, closedness, completeness or smooth
manifold assumption is introduced.

`fullAEL2CuspidalInfiniteRightAction_val` states that the faithful cusp
inclusion carries this action to the published ambient action
`haarQuotientL2InfiniteRightAction`; this is also reflexive.
`norm_fullAEL2CuspidalInfiniteRightAction` inherits norm preservation.
`continuous_fullAEL2CuspidalInfiniteOrbit` composes the already continuous
original full cusp orbit `fullAEL2CuspidalOrbitMap` with the actual infinite
inclusion. `fullAEL2CuspidalInfiniteOrbit_aestronglyMeasurable` derives strong
measurability from that continuity, using the existing Borel measurable
structure and second countability of the original infinite point group,
hence AE strong measurability for any supplied measure on that same group.

`fullAEL2CuspidalInfiniteFinite_commute` applies the existing bounded cusp
action to `AdelicGroupPoints.factors_commute`. It proves the literal
commutation of the original finite cusp action
`fullAEL2CuspidalFiniteRightAction` and this infinite action on every cusp
vector.

`fullAEL2CuspidalOrthogonalProjection_infiniteRightAction` specializes the
published full-adelic intertwining law of the original subtype-valued
orthogonal projection to infinite elements: projecting an ambient infinite
translate equals translating the projection. In the same way
`fullAEL2CuspidalAmbientProjection_infiniteRightAction` states that the
original ambient cusp projection commutes with the ambient infinite action.

For an actual open subgroup `K` of the finite point group with
`[CompactSpace K]`, `fullAEL2CuspidalFiniteAverage_infiniteRightAction` proves
that the existing probability Haar average `fullAEL2CuspidalFiniteAverage`
intertwines this infinite action. It specializes
`compactIsometricAverage_intertwiner` with the bounded operator given by the
original infinite element and the just-proved commutation. The compact
subgroup uses its original subgroup topology and Borel measurable space,
with topological group and second countability properties inherited from the
actual finite adelic group. The existing normalized average and its
integrability remain unchanged.

The provenance is internal restriction and combination of the published
original full cusp action and its projection laws, the ambient infinite
quotient action, the actual adelic product decomposition and the compact
averaging construction. This file supplies no archimedean or simultaneous
smooth-vector density, finite-volume theorem, smooth representative or
automorphic tensor realization, growth, decay, compactness or spectral
assertion.
