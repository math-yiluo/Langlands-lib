# Unipotence via the full centre and the tangent Lie algebra

`Langlands.GroupScheme.Lie.unipotentNilpotentLieCenter` proves
`Langlands.GroupScheme.Lie.UnipotentNilpotentLieCenterStatement.{u}` for a
smooth connected affine group over any field and any closed representative
of its full centre. The Lie bracket is the one on `Additive (lieKernel G k)`
from `instAffineKernelLieRing`.

## Proof

Natural finite tangent coordinates make the tangent space Noetherian.
Engel's theorem then characterizes Lie nilpotence by nilpotence of every
operator `ad X`. The comparison
`adjointDifferentialLieHom_apply_bracket` identifies `ad X` in those
coordinates with the linear map of the actual adjoint tangent matrix.
Conjugation by the coordinate equivalence and the matrix–endomorphism
algebra equivalence preserve and reflect nilpotence. If the group is
unipotent, its closed centre is unipotent by `unipotentClosedSubgroup`, and
`MatrixRepresentation.isNilpotent_tangentMatrix_of_isUnipotent` gives the
required nilpotence for its adjoint representation.

For the converse, factor a torus homomorphism through its closed torus
image using `torusImageClosedTorusStatement`. Restrict the adjoint
representation to that image. Its full scheme-theoretic kernel is a
closed subgroup of a torus, hence of multiplicative type by
`relativeMultiplicativeTypeClosedSubgroup`. Over the field the kernel is
flat and locally of finite presentation. The kernel's conjugation action
fixes the tangent Lie algebra over every coefficient algebra, by
`adjointRepresentation_affineAction` and the kernel equation.
`relativeMultiplicativeTypeCentralizerModel` supplies its smooth closed
centralizer, whose tangent image is the whole Lie algebra.
`RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top` therefore
makes this centralizer the ambient group on every test scheme.

The kernel inclusion consequently factors through the represented centre.
`IsMultiplicativeType.hom_eq_zero_of_isUnipotent` makes that factor zero
because the centre is unipotent. The kernel is trivial, so the restricted
adjoint homomorphism is a monomorphism and its tangent matrix map is
injective. Over a splitting field for the torus, each tangent matrix is
geometrically semisimple by `Lie.isSemisimpleElement_of_isSplitTorus`. It
is also nilpotent by the Lie hypothesis and functoriality of tangent
matrices. It vanishes over the splitting field and hence over the ground
field. Injectivity gives a trivial tangent kernel for the closed torus.
`Lie.points_eq_one_of_subsingleton_lieKernel` makes every scheme-test point
of the torus the identity by smoothness, connectedness and affineness. Thus
every torus homomorphism has trivial range, and `noTorusUnipotent` gives
unipotence over the ground field.

## Source

J. S. Milne, *Algebraic Groups*, 2022 corrected reprint, Corollary 16.61(a,b),
printed pp. 346–347. The formal converse uses the smooth centralizer of the
multiplicative-type kernel on a torus and keeps the argument over the
ground field. The registered source is `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
