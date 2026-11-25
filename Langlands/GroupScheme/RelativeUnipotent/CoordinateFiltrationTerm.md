# Represented filtration terms from supported coordinates

Let an actual group scheme over an arbitrary commutative ring have a scheme
isomorphism from a standard finite polynomial vector scheme. The chart is
only an isomorphism of schemes over the base. Suppose a supplied subgroup
functor is characterized on every scheme test by vanishing coordinates
outside an enumerated subset. This module constructs its smooth closed affine
subgroup scheme on the actual coordinate-subspace scheme.

The inclusion of the coordinate subspace is transported through the chart.
Its points are exactly the supported tuples: extension by zero gives one
direction, and coordinate restriction gives the factorization in the other.
The inclusion is a closed immersion by the coordinate-block closedness
lemma and the chart isomorphism. `SubgroupFunctor.representingGroupScheme`
then transfers the subgroup's own group law to the representing scheme.
Its underlying scheme is definitionally the smaller standard vector scheme,
which proves smoothness and affineness without asserting that the transferred
group law is additive.

This is a derived representability construction using `VectorCoordinateBlock`
and `RepresentabilityTransfer`. Applications to root-height terms must still
prove the displayed all-test coordinate membership condition. This module alone
does not construct their quotient maps or descend the filtration.
