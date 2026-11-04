# Target maps and split-torus coefficients

Author: Worker 1375.

This internal module constructs `Lie.weightSpaceRangeEquiv`: the image of the
differential restricted to a character weight space is naturally the part of
the full differential image lying in that target weight space. The equivalence
leaves the actual target vector unchanged.

First, `Lie.kernelCoefficient_targetMapLinear` proves that reading one
group-algebra coefficient of an actual Lie vector commutes with the actual
differential of a group-scheme homomorphism. Reconstruct the source vector as
the finite sum of its monomial coefficients using
`Lie.kernelCoefficients_reconstruct`. The differential is linear over the
group algebra and commutes with extension of coefficients. For each monomial,
`Lie.kernelCoefficient_monomial` gives the required equality. This step works
over any commutative base ring and any coefficient algebra and commutative
index monoid. Only the source group needs locally finite type in this step.

For a standard split torus over a field,
`splitTorus.characterAdjointCoefficients_targetMapLinear` combines that
coefficient identity with equivariance of the differential under the actual
adjoint actions. Thus the differential commutes with the finite adjoint
coefficient family indexed by actual characters.

For an arbitrary split torus, choose a split-torus isomorphism and use
`weightSpace_comapIso` to transport the characters and their weight spaces.
Given a target weight vector in the full differential image, choose any
preimage and take its coefficient at the corresponding character. The
published coefficient construction puts this vector in the source weight
space; the proved commutation identity maps it to the coefficient of the
original target vector. Since that target vector already has the specified
weight, its coefficient is itself. This proves
`Lie.exists_weightSpace_preimage`.

The equality `Lie.range_weightSpaceMap_eq_comap_range` expresses this
surjectivity onto the intersection, and `Lie.weightSpaceRangeEquiv` is the
linear equivalence induced by equality of the two submodules of the target
weight space.

The field and universe are arbitrary. Both groups are affine and locally of
finite type for the weight-space results, the torus is split, and the
homomorphism is arbitrary. No centrality, smoothness, connectedness, nonzero
character, injectivity or global surjectivity is assumed. All inputs are
proved Library coefficient, differential and weight-space constructions;
the content is derived internally. It is supporting infrastructure for the
central-isogeny root-datum task and does not assert that task's conclusion.
