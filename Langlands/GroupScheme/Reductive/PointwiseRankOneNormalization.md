# Rank-one normalization from pointwise étale Weyl data

This internal derived module isolates the descent step for normalizing
an actual opposite pair over an arbitrary commutative ring. The ambient
group scheme `G` is assumed affine over `Spec R`, as expressed by
`[IsAffineHom G.X.hom]`. The maps are given root parametrizations with an
open triple cell. A prescribed integral torus automorphism and actual
étale Weyl charts through every point are supplied explicitly.

`EtaleRankOneChart` retains its coefficient ring and algebra, its étale
map and a point over the specified base point, actual ring Weyl data
with the same base-changed cell data, and the reflection identity for
the scalar supplied by those Weyl data. No single chart is required
to cover the base.

Under this ambient affineness assumption,
`normalizedOppositePairOfCharts` constructs a global unit scalar and
the prescribed Weyl identity for the pair with its negative map
rescaled by that unit. Affineness supplies the affine chart ambient
groups needed by the dual-coordinate coefficient comparison. The
supporting proof forms the dual-number factorization of the original
open cell once. Its extracted scalar has inverse-beta image on every
supplied chart by the published dual-coordinate base-change theorem.

This original scalar is a unit: otherwise a maximal ideal contains it,
and a chart through that prime would place its unit image in a proper
prime ideal. Its inverse therefore has exactly the beta-unit value on
each chart. The actual scalar Weyl product then normalizes the torus
after each chart pullback. The published pointwise étale equality
criterion for group-scheme homomorphisms descends that identity.

The provenance is composition of the imported open-cell dual-number
calculation, coordinate-preserving base change and pointwise étale
descent with the elementary unit criterion. There is no locality,
reducedness or nontriviality hypothesis on the original ring.
The ambient affineness hypothesis follows from reductivity in the
intended split reductive application.
Constructing the supplied charts and the initial global root
parametrizations from the affine split theorem hypotheses remains a
separate obligation.
