# The original infinite adelic quotient L2 action

Worker 116 constructs `haarQuotientL2InfiniteRightAction` on the unchanged
`Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)`. It is exactly the
existing bounded full adelic quotient right action restricted along the
original continuous homomorphism `AdelicGroupPoints.ofInfinite F G`.
Its pointwise formula is reflexive. No new L2 space, quotient measure,
action or topology is chosen.

The hypotheses are those of the original canonical quotient action:
a number field `F`, an affine locally finite-type group scheme `G`,
a commutative group scheme `T` with a morphism `i`, injective character
restriction of finite-index range, an actual splitting of `T` with finite
index type `I`, centrality of `i`, and right invariance of Haar measure
on the actual norm-one subgroup. This construction does not require
connected reductivity or a smooth manifold. These may be imposed in later
applications while retaining this original action.

`norm_haarQuotientL2InfiniteRightAction` inherits norm preservation.
`continuous_haarQuotientL2InfiniteOrbit` composes the already continuous
original full orbit with the actual infinite inclusion.
`haarQuotientL2InfiniteOrbit_aestronglyMeasurable` uses second countability
of the original infinite point group to obtain strong measurability, hence
AE strong measurability for any supplied measure on that same group.

`haarQuotientL2InfiniteFinite_commute` applies the existing bounded action
to `AdelicGroupPoints.factors_commute`. It proves the literal commutation
of the original finite and infinite actions on every original L2 vector.
For an actual compact open subgroup `K` of the finite point group,
`haarQuotientL2FiniteAverage_infiniteRightAction` proves that its existing
probability Haar average intertwines this infinite action. It specializes
`compactIsometricAverage_intertwiner` with the bounded operator given by
the original infinite element and the just-proved commutation. The compact
subgroup uses its original subgroup topology and Borel measurable space.
The existing normalized average and its integrability remain unchanged.

The provenance is internal restriction and combination of the published
original quotient action, actual adelic product decomposition and compact
averaging construction. This file supplies no archimedean or simultaneous
smooth-vector density, finite-volume theorem, smooth representative or
automorphic tensor realization, growth, decay, compactness or spectral
assertion.
