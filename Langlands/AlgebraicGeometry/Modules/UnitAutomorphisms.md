# The canonical action of global units on module sheaves

This is an internal construction from the published scalar action on actual
scheme-module morphisms. For every scheme `X` and every actual module sheaf
`M : X.Modules`, `Langlands.Scheme.Modules.unitAut M r` multiplies each section
on an open `U` by the restriction of the global unit `r`. Its inverse uses
`r⁻¹`; the two inverse equations follow from the existing linearity of
composition and the unit identities. No local freeness assumption is needed.

`unitAutHom` packages this action as a group homomorphism from `Γ(X, ⊤)ˣ` to
`CategoryTheory.Aut M`. Mathlib multiplies automorphisms by reverse categorical
composition. The proof accounts for that convention using commutativity of
the global section ring. `unitAut_naturality` proves that the action commutes
with every module morphism. Consequently `unitAut_conjugate` shows that
transport through any isomorphism preserves the unit.

For every scheme morphism `f : X ⟶ Y`, `pullback_mapIso_unitAut` identifies
the ordinary pullback of `unitAut M r` with multiplication by the image of `r`
under the actual global section map `f.appTop`. It uses the published
`pullback_map_smul` and preservation of the identity by the pullback functor.
`pullback_mapAut_unitAutHom` records the same square as equality of group
homomorphisms. These assertions apply to arbitrary morphisms and all module
sheaves, including on empty schemes.

The `LineBundle` namespace lifts the construction to the published full
subcategory of actual locally free rank-one sheaves. It includes the group
homomorphism, agreement after forgetting, and compatibility with the ordinary
line-bundle pullback. The objects and automorphisms are not replaced by
isomorphism classes.

The provenance is derived: all claims follow from `ModuleLinear`, the existing
module pullback scalar formula, and full-subcategory isomorphisms. There is
no new literature assertion. This file constructs the action only. It does
not prove that the homomorphism is injective or surjective, even for line
bundles. Those properties require the separate scalar-classification proof;
they are false for arbitrary module sheaves. No smoothness of an automorphism
scheme, stack descent, algebraicity or Picard representability is asserted.
