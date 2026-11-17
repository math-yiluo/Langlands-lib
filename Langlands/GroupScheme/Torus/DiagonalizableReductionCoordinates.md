# Diagonalizable reductions and actual coordinate presentations

This internal interface translates diagonalizable presentations of actual
affine group schemes and their base changes into bialgebra equivalences of
their actual coordinate Hopf algebras. It also reconstructs an actual
diagonalizable group-scheme presentation from such an equivalence. All
constructions work over arbitrary commutative rings, without smoothness,
flatness, noetherianity, or characteristic assumptions.

`DiagonalizableHopfPresentation R C` consists of a finitely generated abelian
character group `N` and a bialgebra equivalence `C ≃ₐc[R] R[N]`.
`hopfPresentationOfIsDiagonalizable` extracts this data when the actual
Hopf spectrum of `C` is diagonalizable in the relative convention. The
relative-model comparison identifies the supplied model with the affine
group-algebra model, and `Diagonalizable.hopfSpecIso` identifies the latter
with the standard Hopf spectrum. Full faithfulness of Hopf spectrum then
gives the required coordinate equivalence, in the contravariant direction.

`affineScalarExtensionIso G` identifies the Hopf spectrum of
`S ⊗[R] AffineCoordinates.hopfAlgebra G` with the actual group-scheme base
change `G_S`. It composes the published Hopf-spectrum base-change comparison
with the base change of the actual affine-coordinate isomorphism.
`diagonalizableScalarPresentation` therefore gives a coordinate presentation
whenever `G_S` is diagonalizable. Its specialization
`diagonalizableReductionPresentation G J hG` applies to `S = R/J`.
No nilpotence assumption on `J` is required to extract this presentation.

`diagonalizableIsoOfCoordinates` converts a supplied bialgebra equivalence
from the coordinates of `G` to `R[N]` into an actual isomorphism `G ≅ D_R(N)`.
When `N` is finitely generated, `isDiagonalizable_of_coordinates` gives the
relative diagonalizable predicate with this same character group. These
interfaces assert no lifting of a coordinate equivalence through an ideal.

The auxiliary affinity lemmas supply the instances needed to form the
coordinate Hopf algebra of a source with the task's finite étale splitting
hypothesis. A relative diagonalizable group is affine over its base because
its group-algebra model is affine and affine morphisms are preserved by base
change and isomorphisms. If a group over an affine base becomes diagonalizable
under a flat surjective affine base change, the published faithfully-flat
affineness-descent theorem makes the original group affine. In particular,
`isAffine_of_finiteEtaleSplit` applies to any supplied finite étale surjective
splitting cover: its covering scheme is affine because it is finite over the
affine base, and an étale morphism is flat.

This is derived content from the published actual affine-coordinate,
Hopf-spectrum, relative diagonalizable-model, and faithfully-flat affineness
descent interfaces. It supplies the scheme-to-Hopf and Hopf-to-scheme
comparisons needed for the deformation argument in Conrad (2014),
Theorem B.3.2(2), pp.288–289. Nilpotent lifting, adic effectivity and the
complete-local deformation theorem remain separate obligations.
