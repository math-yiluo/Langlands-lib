# Unipotence via nilpotent differentials of representations

`Langlands.GroupScheme.unipotentNilpotentDifferential` proves
`Langlands.GroupScheme.UnipotentNilpotentDifferentialStatement.{u}` for
smooth connected affine groups over any field. This is the published
formulation of Milne, *Algebraic Groups* (2017), Corollary 16.61(a), (c),
and (d), printed pp. 346–347, registered as `milne-2017-algebraic-groups`.

## Implemented proof

The implication from unipotence uses
`MatrixRepresentation.isNilpotent_tangentMatrix_of_isUnipotent`.
`affineLinearEmbeddingStatement` supplies a faithful representation since
smoothness implies that the structure morphism is locally of finite type.
The condition for all representations applies to this one in particular.

For the converse, fix a closed-immersion representation whose tangent
matrices over the ground field are all nilpotent. Factor each torus
homomorphism into the group through a closed torus image by
`torusImageClosedTorusStatement`. The restriction to that image is still a
closed immersion and has nilpotent tangent matrices by functoriality.
For each ground-field tangent point of the image, extend it to a field
that splits the torus. `tangentMatrix_baseChange` and
`tangentMatrix_naturality` identify its new matrix with the scalar extension
of its original nilpotent matrix. `Lie.isSemisimpleElement_of_isSplitTorus`
makes the extended matrix geometrically semisimple, so
`Lie.IsGeometricallySemisimpleMatrix.eq_zero_of_isNilpotent` makes it zero.
Injectivity of the field embedding reflects this vanishing.

The faithful restriction has injective tangent matrices, so the raw tangent
kernel of the image torus is a subsingleton. Smoothness, affineness and
connectedness permit `Lie.points_eq_one_of_subsingleton_lieKernel`, which
makes every scheme-test point of the image the identity. This gives trivial
range for the original torus homomorphism, allowing `noTorusUnipotent` to
conclude unipotence over the ground field by Milne's arbitrary-field criterion
(Proposition 17.81, printed p. 378).
