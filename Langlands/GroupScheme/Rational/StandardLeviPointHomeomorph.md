# The inherited point topology on an actual represented standard Levi

Authors: Worker 289 and Worker 34. Worker 34 requested the topology comparison
needed for actual rational Levi norms; Worker 289 implemented this adapter.

This is an internal derivation from the published
`PointTopology.rationalPointSubgroupHomeomorph` and
`standardLeviRationalPointsEquiv`. It introduces no new structural assertion
about reductive groups.

Over an arbitrary topological field `F`, let the affine group scheme `G`, the
commutative group scheme `T`, the morphism `i`, the cocharacter `ν` and the
character set `J` be exactly those in `standardLevi i ν J`. Suppose this
all-test subgroup functor is represented by `j : M → G`, and suppose `j` is
a closed subgroup inclusion. The source scheme is affine because its map
into affine `G` is a closed immersion. No reductivity, genericity, torus
maximality, local compactness or separation premise is required.

`standardLeviRationalPointsHomeomorph` specializes the published
represented-subgroup homeomorphism to this exact functor. Its source has
`rationalPointTopology F M.X`. Its target has the subtype topology inherited
from `rationalPointTopology F G.X`. This inherited topology is the same
induced topology named `standardLeviPointTopology`; it is not defined by
transport from `M(F)`. The module installs these topologies only locally.
The field, schemes, and test objects retain their arbitrary universe `u`.

The theorem `standardLeviRationalPointsHomeomorph_toMulEquiv` proves equality
of the underlying multiplicative equivalence with the already published
`standardLeviRationalPointsEquiv`. Both forward maps send `x` to
`rationalPoints.map j x`, with codomain restricted to the actual standard
Levi subgroup. Extensionality and subtype extensionality prove equality;
the application theorem exposes the identical ambient point. Thus the
homeomorphism upgrades the existing algebraic identification without choosing
another Levi or changing either topology.

The proof imports `PointTopology.RepresentedSubgroup`, whose generic
homeomorphism uses the closed-immersion point embedding, and
`Rational.StandardLeviPointComparison`, which supplies the original
algebraic equivalence. These published definitions and proofs provide all
provenance for the adapter. The module adds no original-literature claim,
no connected-reductivity theorem, and no representation-theoretic input.
