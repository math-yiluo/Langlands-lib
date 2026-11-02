# Fibre products for the actual scheme point topology

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1 and its gluing proof, printed page 4.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`SchemePointPullbackProperty R S` states that the canonical map from actual
relative `S`-points of any limiting pullback cone over `Spec R` to compatible
pairs of points is a homeomorphism. The map is precisely
`p ↦ (p ≫ c.fst, p ≫ c.snd)`. Despite its existing
`affineSchemePullbackPointComparison` name, that published map and its
set-level equivalence have no affineness hypothesis.

The source point space has the published `schemePointTopology`. The target
has the subspace topology from the product of the two scheme point
topologies. Its equation is equality of the two composites to the common
target scheme; their common point is allowed to vary.

The coefficient ring `R` and its commutative value algebra `S` lie in a common
arbitrary universe. Only `S` is topologized. It is a topological local ring
satisfying `IsOpenUnits`, which includes openness of its unit locus and
continuity of inversion there. No Hausdorffness, separation or finiteness
hypothesis is imposed.

This target is a derived strengthening of the fibre-product clause of
Proposition 3.1: it permits arbitrary relative schemes and a distinct value
algebra. The affine-chart proof uses local-ring factorization, open affine
charts and the affine pullback comparison, without finite type. Taking
`S = R` and restricting to locally finite type schemes recovers the source
clause. This file states the property and does not supply its proof.
