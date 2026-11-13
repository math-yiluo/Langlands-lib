# Module sheaves on a basis and on all opens are equivalent

Module `Langlands.Sheaf.Renard.ModuleBasisChange`, namespace
`Langlands.Sheaf.Renard.ModuleBasisChange`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The last paragraph of II.2.1, printed p.37 / PDF p.43, proves the equivalence for sheaves of
abelian groups:

> Terminons cette section en remarquant que la catégorie des faisceaux sur `X` de base `T₀`
> est équivalente à la catégorie des faisceaux de base `T`. On passe de manière évidente d'un
> faisceau de base `T` à un faisceau de base `T₀`, par restriction. Dans l'autre sens, si `F`
> est un faisceau de base `T₀` et si `U` est un ouvert quelconque de `X`, on définit `F⁺(U)`
> comme l'ensemble des sections `s : U → ∐_{x∈U} F_x` exactement comme en (II.2.1.2). […]

The II.2.5 Remark (printed p.39 / PDF p.45) uses this paragraph for sheaves of
`𝒞^∞_X`-modules, which are sheaves of modules in the sense of II.2.3 (printed p.38 / PDF
p.44): "De plus, en vertu du dernier paragraphe de II.2.1, ceci reste vrai pour les faisceaux
de base `T`." Here `T` is the set of all opens and `T₀` a basis, in Renard's case the compact
opens `T_c`.

The Library has the additive equivalence as `BasisAllOpen.equivalence`
([BasisAllOpenEquivalence](BasisAllOpenEquivalence.md)) and the category of module sheaves of
II.2.3 as `BasisModuleSheaf` ([RingedBasisModules](RingedBasisModules.md)). It has no basis
change for module sheaves. This file lifts the published additive equivalence to module sheaves
over a ring presheaf defined on all opens. It then specializes the result to the locally
constant scalars `𝒞^∞_X`, for an arbitrary basis and for Renard's `T_c`. Every declaration is a
definition or a proved theorem. There is no proposition for a later proof task.

## Setting

- `X : Type u` is any topological space and `B : OpenBasis X` any published chosen basis. As
  in the published additive equivalence, there is no further hypothesis.
- `R : (Opens X)ᵒᵖ ⥤ RingCat` is a ring presheaf on **all** opens. `basisRing B R` is its
  restriction to `B`, and `allOpenRing R` its restriction to the published basis of all opens.
  Renard's ringed spaces are of this kind: `𝒞^∞_X` is defined on every open. A ring presheaf
  given only on `B` would first have to be extended, which the source does not need.
- Module sheaves are the published `BasisModuleSheaf` (Mathlib presheaves of modules whose
  underlying additive presheaf satisfies Renard's sheaf condition). Their sections live in
  universe `max u v`, as in `BasisAllOpen.equivalence`.

## The extension functor

- `restrictScalar a U` restricts a scalar `a ∈ R(V)` to a basis member `U ⊆ V`, as an
  element of the basis ring `R(U)`. `restrictScalar_one`, `_mul`, `_add`, `_zero` are the ring
  homomorphism laws. `ringRestriction_restrictScalar` and `restrictScalar_restrict` are
  functoriality of `R`, proved through the thinness of the category of opens.
- `familySMul M a s` is the componentwise action `(a • s)_U = a|_U • s_U` on a compatible
  family `s` in the published `BasisAllOpen.Families`. Compatibility of the result is the
  semilinearity of the restrictions of `M` (`BasisModuleSheaf.restrict_smul`). `familyModule`
  makes the families over `V` an `R(V)`-module; each module law is checked componentwise.
  `familySMul_apply` and `family_smul_apply` give the formula.
- `extensionSheaf M` is the published additive extension `BasisAllOpen.extension` of the
  underlying sheaf of `M`, and `extensionModule` puts `familyModule` on its sections.
  `extension_semilinear` says that restriction of families (discarding components) is
  semilinear along the ring restriction.
- `extensionObj M` is the module sheaf obtained with the published adapter
  `BasisModuleSheaf.ofBasisSheaf` ([RingedBasisModuleAdapter](RingedBasisModuleAdapter.md)).
  `extensionMap φ` is the published additive extension of `φ`. It preserves the action
  because each component of `φ` is linear. `extension B R` is the functor.

## The restriction functor

- `restrictionSheaf N` is the published `sheafBasisRestriction` of the underlying sheaf of `N`.
  `restrictionModule` keeps the module structure of `N` on each basis member. The ring is the
  same, since `(basisRing B R)(U) = R(U) = (allOpenRing R)(U)`.
- `restriction_semilinear` is the semilinearity of `N` itself, and `restrictionObj`,
  `restrictionMap` and `restriction B R` are the restricted module sheaf, morphism and functor.

## The equivalence

- `unitLinearEquiv M U` is the published additive `basisSectionIso` (a section on a basis
  member goes to the family of its restrictions). It is `R(U)`-linear by the semilinearity of
  `M`. `unitObjIso M` assembles these maps with Mathlib's `PresheafOfModules.isoMk`;
  naturality is the published `basisSectionIso_restriction`.
- `counitSymmLinearEquiv N V` is the inverse of the published gluing `counitSectionIso`
  (a section goes to its family of restrictions). It is `R(V)`-linear by the semilinearity of
  `N`. `counitObjIso N` uses its inverse, the published gluing, and naturality is the
  published `counitSectionIso_restriction`.
- `equivalence B R : BasisModuleSheaf (basisRing B R) ≌ BasisModuleSheaf (allOpenRing R)` has
  functor `extension B R`, inverse `restriction B R`, and the unit and counit above. Their
  naturality is the published `basisSectionIso_naturality` and `counitSectionIso_naturality`.
  The triangle identity is the published `BasisAllOpen.extension_unit_counit`, read
  componentwise, because the module unit and counit have the same underlying maps.
- `extension_forget` and `restriction_forget` say that forgetting the module structures gives
  exactly the published additive functors `BasisAllOpen.extension` and `sheafBasisRestriction`.
  So this equivalence is the published additive equivalence with module structures added.

## `𝒞^∞_X`-modules

- `ScalarModuleSheaf B` is the category of sheaves of `𝒞^∞_X`-modules on the basis `B`: module
  sheaves over the published ring presheaf `LocallyConstantScalar.basisRingPresheaf B ℂ` of
  locally constant functions. `ScalarModuleSheaf (allOpenBasis X)` unfolds to the category
  `ModuleSheaf X` of the II.2.5 Remark unit `VectorSheafModuleEquivalence` (a separate unit,
  not imported here).
- `scalarEquivalence B : ScalarModuleSheaf B ≌ ScalarModuleSheaf (allOpenBasis X)` is
  `equivalence` for `R = LocallyConstantScalar.ringPresheaf X ℂ`.
- `compactScalarEquivalence hX` is the case of Renard's basis `T_c` of compact opens of a t.d.
  space (the published `ProjectorBasisSheaf.compactOpenBasis hX`).

Composing `compactScalarEquivalence` with the all-open equivalence between complex vector
sheaves and sheaves of `𝒞^∞_X`-modules (`VectorSheafModuleEquivalence.equivalence`) gives the
base-`T_c` form of the II.2.5 Remark. That composite is not constructed here, because the
all-open equivalence is not in the Library at this file's base. It is a one-line follow-up.

## Provenance

The equivalence is the source's basis-change paragraph of II.2.1, for the module sheaves of
II.2.3, as used in the II.2.5 Remark. The componentwise action on families, the linearity of
the published unit and counit maps, and the specializations are this file's construction on
top of the published additive equivalence. The source treats the module case as evident.
Worker 4 wrote this unit for the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`
(Task 1222), in agreement with Worker 1222.
