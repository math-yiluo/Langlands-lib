# Affine torsors from natural simply transitive actions

This internal construction supports the relative Levi torsor proof. It
combines the published affine cocycle torsor with the singleton sheaf
condition on a natural presheaf action. Its intended application is the
conjugation action on actual Levi images, following Brian Conrad,
*Reductive group schemes* (2014), Corollary 5.4.6, p.178, source identifier
`conrad-2014-reductive-group-schemes`.

`Action` records a group action on every test object's sections, natural
under restriction, with a unique group point taking any supplied section
to any other supplied section. It does not assert the existence of global
sections.

For the affine construction, assume `S` is affine, `G` has affine structure
morphism `G → S`, and `F` has an `Action G F` as above. Assume also that `F`
satisfies `Presieve.IsSheafFor F (.singleton p)` for every surjective étale
morphism `p : V → W` of `S`-scheme tests. Finally, supply a section `x` over
an affine surjective étale cover `U → S`. Smoothness of the resulting model
requires the additional assumption that `G → S` is smooth.

A section over a cover defines a difference cocycle, oriented to take the
second pullback of that section to the first. Over an affine base and an
affine surjective étale cover, with the affine acting group and singleton
descent hypotheses just stated, the published `CocycleTorsor` construction
gives an actual affine scheme with group action. The section on its
trivializing cover is invariant under the cocycle relation and hence
descends by the singleton sheaf condition. Evaluation of this descended
section has the prescribed formula on the trivializing cover.

Evaluation is equivariant: restrict a point of the model to the pullback of
its presentation cover, apply the explicit formula there, and use sheaf
separation. It is injective because the scheme torsor has a unique group
difference and the presheaf action is free. It is surjective by pulling a
given test scheme back along the original cover, writing its section as a
unique group translate of the supplied local section, and descending the
resulting morphism to the model along an effective epimorphism. Injectivity
ensures the local morphisms match; sheaf separation verifies the descended
point has the required value.

`Action.representation` packages these natural bijections as an actual
representation of the presheaf. Using the affineness of `G → S`, the model
is affine over the affine base,
surjective, smooth when the group is smooth, and its actual `leftSMul`
morphism is an isomorphism. These geometric assertions are inherited from
the published cocycle torsor. No section over the original base or
vanishing of torsor cohomology is assumed.
