# Diagonal pairs and restriction of quotient covers in action diagrams

This is internally derived infrastructure for the finite-type system in the
Noetherian first-level construction. Its provenance is the published action,
diagonal pair, cartesian diagram, invariant-cover descent and scheme-quotient
constructions. The underlying geometric operations are fibre products,
restriction of an inverse system, and gluing of affine quotients. They implement
the base-change and quotient steps of the proof of Stacks Project,
Proposition 70.8.1, Tag 07SU (registered source
`stacks-noetherian-approximation-2026-11-01`), with the finite invariant covers
already constructed in the Library. All declarations work in arbitrary
universe `u`.

For an action diagram `A` over a diagram `D` of étale equivalence relations,
`ActionDiagram.pair` has points `P_i ×_{D_i.U} P_i`, structure map the first
projection followed by the original structure map, and action
`(A.action i).pairAction`. Its transitions are `Action.pairObjMap`.
The functor laws are checked on both projections. Equivariance is the
published diagonal-pair equivariance, and the structure-map pullback squares
follow by pasting the pair-projection square with the original square.
`ActionCone.pair` makes the same construction for an action over the cone
point, with pair maps as its legs. Its cone equations are checked on the two
projections and its squares follow by the same pasting argument.

`ActionDiagram.whisker` restricts the diagram along a supplied functor, and
`ActionCone.whisker` restricts its compatible cone action. All structure maps,
actions, legs, equivariance and pullback squares are inherited at the selected
indices and morphisms.

For a finite invariant affine quotient cover `C`,
`InvariantAffineQuotientCover.schemeQuotient` chooses the scheme quotient
obtained by the published gluing theorem. The following instance proves its
quotient map affine by applying the published affineness theorem to the same
cover; it does not infer that the whole quotient scheme is affine.

Assume every object scheme `(D.obj i).U` is affine and the index type `K`
is finite. These are additional hypotheses, separate from a descended
invariant affine quotient cover model `M`.
`CartesianDiagram.InvariantAffineQuotientCoverModel.coverAt a` packages the
preimages of its opens along a transition `a : j → M.index` as a finite
invariant affine quotient cover at level `j`. Covering follows because inverse
image preserves suprema and the top open, and finiteness follows from `Finite K`.
The transition on object schemes is a morphism between affine schemes, hence
is affine; its inverse images of affine opens are therefore affine. Invariance
is preserved by cartesian inverse image. The same affine-object hypotheses
support the published cartesian affine-quotient theorem that pulls back each
affine chart quotient.
