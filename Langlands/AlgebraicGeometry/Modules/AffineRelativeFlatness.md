# Relative flatness and flat sections on affine schemes

This is an internal derivation from the existing actual stalk definition of
relative flatness, Mathlib's affine associated-sheaf localization maps, and
its module flatness criterion. Let `φ : A → B` be a morphism of commutative
rings, in any scheme universe. The action of `A` on a `B`-module is always
restriction along this actual `φ`, implemented by `Module.compHom`.

`flat_moduleSpecΓFunctor_of_isFlatOver` proves that the actual affine section
module of a quasi-coherent ordinary module sheaf `M` on `Spec B` is flat over
`A` if `M` is relatively flat over `Spec A` along `Spec.map φ`. Relative
flatness is the existing `IsFlatOver`: every actual sheaf stalk is flat over
the base local ring at its image through the actual morphism's stalk map.
No finite presentation, noetherian, or flatness assumption on `B` is required.

The implemented proof first treats an associated sheaf `tilde N`.
`flat_stalk_tilde_of_isFlatOver` restricts its relatively flat stalk along
`A → O_{Spec A, φ(x)}`. This local ring is an actual localization of `A`,
so it is flat over `A`. The scalar tower is checked explicitly with
`stalkMap_toStalk_apply`: restricting along the base local ring and the
actual `Spec.map φ` stalk map gives the same action as `A → B` followed by
the canonical stalk action. Transitivity then gives stalk flatness over `A`.

`flat_of_isFlatOver_tilde` applies `Module.flat_of_isLocalized_maximal` with
auxiliary algebra `B`. At each maximal ideal of `B`, the canonical
`tilde.toStalk` map is the required module localization, and the preceding
stalk result supplies flatness over `A`. This proves flatness of `N`.
For arbitrary quasi-coherent `M`, the actual comparison `M.fromTildeΓ` is an
isomorphism. Invariance of relative flatness under that isomorphism reduces
the section-module theorem to the associated-sheaf case.

`affineFlatModules φ` is the object property of `B`-modules flat over `A`
with the specified restricted action. `flatAffineSectionsFunctor φ` is the
ordinary `moduleSpecΓFunctor` restricted from the full subcategory of
quasi-coherent sheaves relatively flat along `Spec.map φ` to the full
subcategory defined by `affineFlatModules φ`. On objects and arrows it uses
the existing affine section functor; its new property proof is exactly the
section-flatness theorem above. The module proves this implication only;
it does not assert the converse, a deformation existence theorem, or an atlas.
