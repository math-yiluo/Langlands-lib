# Renard III.3.1: the equivariant comparison maps and the conditional equivalences

Worker 134 implemented this module. It is the helper module of the proof of
`Langlands.Sheaf.Renard.EquivariantModuleStatements.Statements`. All
declarations are in `Langlands.Sheaf.Renard.EquivariantModuleEquivalence`.

## Source and route

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, III.3.1, printed p.83 /
PDF p.89. Renard defines an action of `G` on a sheaf `F` and observes, in one
sentence: "Grâce à l'équivalence de catégories du II.2.5, on voit que la
donnée d'un faisceau muni d'une action de `G` est équivalente à la donnée
d'un `𝒟(X)`-module non dégénéré, muni d'une action linéaire de `G`
compatible avec celle de `𝒟(X)`." III.3.2, printed p.84 / PDF p.90, then
restricts this correspondence to smooth actions. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF
pp.89–90 were read for this module.

The module makes Renard's sentence precise. The published II.2.5
comparisons are the sheaf map `F ⟶ P(Γc F)` and the module map
`M ⟶ Γc(P M)`. This module checks that both commute with the original group
operators. They therefore become the unit and the inverse counit of an
equivalence between the published equivariant functors. Their
invertibility is reduced to the two published II.2.5 propositions
`CompactSectionEquivalence.SheafComparisonIsIso` and
`ModuleProjectorComparison.ModuleComparisonIsIso`. Those propositions enter
only as hypotheses `hS` and `hM` of the declarations below. The entry module
`EquivariantModuleProof` supplies their published proofs.

## Germ transport

`Γgerm_global_inv F k t x y (h : k • x = y)` states the following. The
global germ at `x` of `globalRepresentation F k⁻¹ t` equals the published
labelled stalk transport `Godement.stalkPull F.obj k x y h` applied to the
global germ of `t` at `y`. Here `globalRepresentation` is the published
original operator on global sections. The proof identifies the operator of
`k⁻¹` with restriction along the labelled arrow `⊤ ⟶ ⊤` with label `k`. It
then applies the published germ formula `Godement.germ_stalkPull_arrow`.

## The sheaf-side comparison

Fix an action sheaf `F : ActionSheaf G X` and write `underlying F` for its
published underlying vector sheaf. `SheafProjectorComparison.family` sends a
section `s` over an open `V` to the family of zero extensions of `s|_W`,
indexed by the compact opens `W ⊆ V`.

- `family_familyPull` shows that this family commutes with every labelled
  arrow `f : U ⟶ V` of `ActionOpens G X`. On the target side the arrow acts
  by the published `ProjectorActionSheaf.familyPull` of the compatible
  module `CompactSectionActions.compatibleObject hX F`. The two families are
  compared componentwise by global germs (`ext_compact`). At a point `x`,
  `Γgerm_global_inv` moves the germ of the translated component to the
  point `f.label • x`. If `x` lies in the compact open `W`, then
  `f.label • x` lies in the translated compact open
  `ProjectorActionSheaf.translatedInside hX f W`. Both germs are then given
  by `Γgerm_extension_of_mem`, and `germ_stalkPull_arrow` identifies them.
  Otherwise both germs vanish by `Γgerm_extension_of_not_mem`.
- `unitHom hX F : F ⟶ (ProjectorActionSheaf.functor hX).obj
  ((CompactSectionActions.functor hX).obj F)` is the morphism of action
  sheaves whose component at a transport object `U` is the published
  ordinary component `SheafProjectorComparison.sheafComparisonApp` on the
  underlying open `U.openSet`. Its naturality over all labelled arrows is
  `family_familyPull`. `unitHom_app` records by `rfl` that each component is
  the published `sheafComparison` component on the same open.
- `unitNat hX : 𝟭 (ActionSheaf G X) ⟶ CompactSectionActions.functor hX ⋙
  ProjectorActionSheaf.functor hX` has components `unitHom hX F`.
  Naturality in `F` is the published `familyMap_family`.
- `isIso_unitHom` assumes that the ordinary comparison of `underlying F` is
  an isomorphism and concludes that `unitHom hX F` is one. Every component
  is then invertible, so `NatIso.isIso_of_isIso_app` gives an isomorphism of
  presheaves on `ActionOpens G X`. `ObjectProperty.isIso_hom_iff` lifts it
  to the full subcategory of sheaves.

## The module-side comparison

Fix `M : CompatibleTestAction.{uG, 0, 0} G X`.

- `counitInvModule hX M` is the published module comparison
  `ModuleProjectorComparison.moduleComparison hX M.module`. It is followed by
  the compact-section functor applied to the inverse of the published
  identity-component isomorphism `ProjectorActionSheaf.underlyingSheafIso`.
  `counitInvModule_val` records by `rfl` that `m` goes to the original-vector
  global section `ProjectorVectorSheaf.originalFamily hX ⊤ m`.
- `counitInvModule_comm` shows that this map intertwines `M.action g` with
  the published compact-section operator of `g` on the reconstructed action
  sheaf. This is the published `SmoothProjectorActionSheaf.global_originalFamily`.
  `counitInvHom hX M` packages the map and this law as a morphism of
  compatible test actions.
- `counitInvNat hX : 𝟭 ⟶ ProjectorActionSheaf.functor hX ⋙
  CompactSectionActions.functor hX` has components `counitInvHom hX M`.
  Naturality reduces, componentwise on compact opens `U`, to linearity of a
  module morphism `φ` for the characteristic test function of `U`:
  `φ(χ_U · m) = χ_U · φ(m)`.
- `isIso_of_isIso_moduleHom` holds for any morphism `f` of compatible test
  actions whose underlying module morphism is invertible. Then `f` is
  invertible: the inverse module morphism again commutes with the group
  operators, by the two inverse identities.
- `isIso_counitInvHom` assumes that the published module comparison of
  `M.module` is an isomorphism and concludes that `counitInvHom hX M` is one.
  `counitInvModule` is then a composite of two isomorphisms.

## The conditional equivalences

In the section `Conditional` the hypotheses are
`hS : CompactSectionEquivalence.SheafComparisonIsIso` and
`hM : ModuleProjectorComparison.ModuleComparisonIsIso`.

- `isIso_unitNat` and `isIso_counitInvNat` apply `hS` and `hM` to every
  object, then `NatIso.isIso_of_isIso_app`.
- `equivalence hX hS hM : ActionSheaf G X ≌ CompatibleTestAction.{uG, 0, 0} G X`
  is Mathlib's `CategoryTheory.Equivalence.mk` applied to
  `CompactSectionActions.functor hX`, `ProjectorActionSheaf.functor hX`, the
  unit `asIso (unitNat hX)` and the counit `(asIso (counitInvNat hX)).symm`.
  `Equivalence.mk` keeps both functors and the counit. It replaces the unit
  by its adjointified form so that the triangle law holds.
  `equivalence_functor` and `equivalence_inverse` record that the functor
  and the inverse are exactly the published functors, by `rfl`.
- With `[IsTopologicalGroup G]` and `hG : IsLocallyProfinite G`,
  `smoothUnitIso` and `smoothCounitIso` restrict the unit and counit
  isomorphisms of `equivalence` to the published whole-module smooth full
  subcategories. Each component is lifted by `ObjectProperty.isoMk`. The
  composites `CompactSectionActions.smoothFunctor hX ⋙
  SmoothProjectorActionSheaf.smoothFunctor hX hG` and the reverse composite
  have definitionally the objects and maps of the ambient composites, so
  the ambient components fit and naturality is the ambient naturality.
- `smoothEquivalence hX hS hM hG : SmoothActionSheaf G X ≌
  CompactSectionActions.SmoothCompatibleTestAction` is
  `CategoryTheory.Equivalence.mk` applied to the two published smooth
  functors and these restricted isomorphisms. Its functor and inverse are
  again the published smooth functors, by `rfl`. No smooth-vector functor is
  used.

`statements_of_comparisons hS hM : EquivariantModuleStatements.Statements`
proves both conjuncts of the published target. For each `G` and `X` it
supplies `equivalence` or `smoothEquivalence` with the two functor equalities
by `rfl`. The group premise `hG` of `AlgebraicStatement` is not needed for
the algebraic equivalence. No hypothesis besides `hS` and `hM` is added, and
no inverse functor law or equivalence is assumed.
