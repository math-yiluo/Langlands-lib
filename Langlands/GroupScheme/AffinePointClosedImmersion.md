# Closed immersions on actual affine group points

Author: Worker 112.

This internal adapter uses the existing regular-function evaluation topology
on actual group-scheme points. It is derived from the published
`affinePointsRingPointHomeomorph` and the actual affine-scheme point mapping
theorems, without a new literature assertion.

Let `G` and `H` be affine group schemes over an arbitrary commutative ring `R`
and `A` an `R`-algebra with a topology. The existing homeomorphisms identify
the group-point and general affine-scheme point topologies by the identity
on actual relative scheme morphisms. The point map of a group-scheme
homomorphism `f : G ⟶ H` is postcomposition by its actual underlying
relative scheme map.

If the underlying scheme map is a closed immersion, the published
`isEmbedding_affineSchemePointMap` applies. Composing it with the existing
identity homeomorphisms proves `isEmbedding_affinePointsTarget`. If `A` is
Hausdorff, the same transport of `isClosedEmbedding_affineSchemePointMap`
proves `isClosedEmbedding_affinePointsTarget`. The implemented proofs simplify
the two homeomorphisms to the identity on actual morphisms. The reused scheme
mapping theorems derive their results from surjectivity of the actual
coordinate pullback and algebra-point precomposition.

No finite-type hypothesis, topology on the base or coordinate algebra, or
continuity of ring operations on `A` is required. The result does not assert
that an arbitrary group-scheme homomorphism is a closed immersion.
