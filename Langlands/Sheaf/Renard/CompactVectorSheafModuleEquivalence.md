# Complex vector sheaves and sheaves of `𝒞^∞_X`-modules on a basis are equivalent

Module `Langlands.Sheaf.Renard.CompactVectorSheafModuleEquivalence`, namespace
`Langlands.Sheaf.Renard.CompactVectorSheafModuleEquivalence`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Source

The Remark after the Proposition of II.2.5, printed p.39 / PDF p.45:

> Remarque. Il est évident que réciproquement, un faisceau de `𝒞^∞_X`-modules est
> naturellement un faisceau de `ℂ`-espaces vectoriels sur `X`. […] Ainsi les notions de
> faisceau de `ℂ`-espaces vectoriels sur `X` et de faisceau de `𝒞^∞_X`-modules sont
> équivalentes (i.e. les catégories respectives sont équivalentes). De plus, en vertu du
> dernier paragraphe de II.2.1, ceci reste vrai pour les faisceaux de base `T`.

The Proposition just before (printed pp.38–39 / PDF pp.44–45) makes a complex vector sheaf
of base `T_c` (the compact opens of a t.d. space) a sheaf of `𝒞^∞_X`-modules by
`(f s)(x) = f(x) s(x)`. The last paragraph of II.2.1 (printed p.37 / PDF p.43) says that
sheaves on a basis `T₀` and sheaves on all opens `T` form equivalent categories.

## What the Library already has

- `VectorSheafModuleEquivalence.equivalence X : VectorSheaf X ≌ ModuleSheaf X`
  ([VectorSheafModuleEquivalence](VectorSheafModuleEquivalence.md)) is the Remark for
  sheaves on all opens. Its Markdown lists the base-`T_c` form as a remaining obligation.
- `ModuleBasisChange.scalarEquivalence B : ScalarModuleSheaf B ≌ ScalarModuleSheaf
  (allOpenBasis X)` and its case `compactScalarEquivalence hX` for `T_c`
  ([ModuleBasisChange](ModuleBasisChange.md)) give the last paragraph of II.2.1 for sheaves
  of `𝒞^∞_X`-modules.

The Library's complex vector sheaves `VectorSheafScalars.VectorSheaf X` are Mathlib sheaves
of complex vector spaces on all opens. The Library has no separate category of complex
vector sheaves on a basis; the published additive `BasisAllOpen.equivalence` identifies
sheaves on a basis with sheaves on all opens. So with the Library's convention, the base-`T_c`
form of the Remark is an equivalence between `VectorSheaf X` and the sheaves of
`𝒞^∞_X`-modules on `T_c`. This file constructs it as a composite of the two published
equivalences. It discharges the obligation left open in
[VectorSheafModuleEquivalence](VectorSheafModuleEquivalence.md).

## Declarations

`X : Type u` is a topological space. `B` is any published `OpenBasis X`.

- `moduleSheaf_eq` (proved by `rfl`): the category `ModuleSheaf X` of the all-open unit is
  the category `ScalarModuleSheaf (allOpenBasis X)` of the basis-change unit. This is why the
  two equivalences compose without a transport.
- `basisEquivalence B : VectorSheaf X ≌ ScalarModuleSheaf B` is
  `(VectorSheafModuleEquivalence.equivalence X).trans (ModuleBasisChange.scalarEquivalence B).symm`.
  It is the Remark for sheaves of `𝒞^∞_X`-modules of base `B`.
- `compactEquivalence hX : VectorSheaf X ≌ ScalarModuleSheaf (compactOpenBasis hX)`, for a
  locally profinite (t.d.) space with `hX : IsLocallyProfinite X`, is
  `(VectorSheafModuleEquivalence.equivalence X).trans (ModuleBasisChange.compactScalarEquivalence hX).symm`.
  Here `ProjectorBasisSheaf.compactOpenBasis hX` is the published basis `T_c` of compact
  opens. `compactEquivalence_eq` records, by `rfl`, that it is `basisEquivalence` for this
  basis.

The remaining lemmas describe the composite. All are proved by `rfl`.

- `basisEquivalence_functor`: the functor is the published `VectorSheafModuleEquivalence.toModule X`
  (the locally constant action) followed by the published
  `ModuleBasisChange.restriction B (LocallyConstantScalar.ringPresheaf X ℂ)` (restriction to
  the basis).
- `basisEquivalence_inverse`: the inverse is the published `ModuleBasisChange.extension`
  (extension from the basis to all opens by compatible families) followed by the published
  `VectorSheafModuleEquivalence.toVector X` (restriction of scalars to the constants).
- `basisEquivalence_sections`: over a basis member `U`, the module of sections of the image of
  `F` has the sections of `F` over `U` as its underlying type.
- `basisScalar f` is a locally constant function `f` on a basis member `U`, read as an element
  of the ring `𝒞^∞(U)` of the basis ring presheaf. It is the identity map and only fixes the
  type for the action.
- `basisEquivalence_smul`: on these sections, `basisScalar f • s` is the published locally
  constant action `VectorSheafScalars.smul F f s`. This action is the glued section with germs
  `f(x) s(x)`, as in the Proposition.
- `basisEquivalence_map_app`: the image of a morphism `φ` has the components of `φ` over basis
  members.

## Provenance

The equivalence is the base-`T` clause of the source Remark. The source cites the last
paragraph of II.2.1 and gives no further proof. The construction as a composite of the
published all-open equivalence and the published module-sheaf basis change is this file's
own. Worker 4 wrote this unit for the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`
(Task 1222), in agreement with Worker 1222. Every declaration is a definition or a proved
theorem, so no proof task is needed.
