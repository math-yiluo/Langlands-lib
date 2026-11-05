# Actual relative roots of monomorphic subgroup representatives

Author: Worker 1623.

This internal comparison concerns actual adjoint Lie weights over any field,
with the field and group universe unrestricted. If `a : T → H` is a torus map
and `p : H → G` is a homomorphism of affine group schemes whose underlying
morphism over the base is monomorphic, `relativeRoots a` equals
`RelativeRoot.subgroupRelativeRoots (a ≫ p) (SubgroupFunctor.range p)`.
`relativeRootsEquivSubgroupRelativeRoots` constructs the resulting equivalence
of root types. It preserves each character literally. The torus need not be
split for this comparison.

For a split torus acting on an affine group locally of finite type,
`subgroupRelativeRoots_dynamicParabolic` identifies the nonzero ambient
weights supported by the dynamic parabolic with the actual ambient roots
whose integer pairing with its cocharacter is nonnegative. If that
cocharacter is generic, these are exactly its positive relative roots.
`relativeRoots_parabolicRepresentative_of_generic` consequently identifies
the intrinsic roots of any affine representative of that dynamic parabolic
with the positive ambient roots, provided the actual torus lift composes to
the ambient torus map.

The proof first checks conjugation equivariance on every test scheme using
the pointwise multiplication and inverse laws for group-scheme
homomorphisms. The published monomorphic weight-transfer theorem
`mem_actionWeightSupport_range_iff` then identifies the nonzero source weight
spaces with ambient support. The comparison between conjugation weight
spaces and adjoint weight spaces, followed by deletion of the zero
character, gives the root equality and its character-preserving equivalence.
For the parabolic comparison, the published
`tangentSubmodule_parabolic_eq_semigroupWeightSpan` gives the exact
nonnegative Lie image. `HasLieImage.mem_actionWeightSupport_iff` recovers
its weight support from that equality. Removing the zero character and
using genericity gives the positive root set.

Provenance is derived: all results follow from the cited published Library
definitions and proofs, without an additional assertion from the literature.
The parabolic support comparison assumes no smoothness, connectedness or
reductivity. Empty root sets are allowed. This module does not assert
geometric minimality or any compactness or adelic coverage result.
