/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# Sections of quasi-coherent modules over basic opens of an affine open

Let `M` be a quasi-coherent `𝒪_X`-module, `W` an affine open subscheme of `X` and `f ∈ Γ(X, W)`.
Then the restriction `Γ(M, W) → Γ(M, D(f))` is a localization at the powers of `f`. We record the
two halves of this statement elementwise: every section over `D(f)` becomes, after multiplication
by a power of `f`, the restriction of a section over `W`; and a section over `W` vanishing on `D(f)`
is killed by a power of `f`.

We also record the finite-presentation analogues of Mathlib's results on quasi-coherent modules:
finite presentation is preserved by restriction to open subschemes, is local on open covers, and
on the spectrum of a Noetherian ring is detected by finiteness of the global sections.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen`
- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen`
- `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`: the two halves together.
- `AlgebraicGeometry.Scheme.Modules.flat_sections_of_isInvertible`: the sections of an invertible
  module over an affine open are flat.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_restrictFunctor`: restriction along an
  open immersion preserves finite presentation.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`: pullback along any morphism of
  schemes preserves quasi-coherence.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_isOpenCover` and
  `isFinitePresentation_of_iSup_opensRange_eq_top`: a module with finite presentations locally on
  an open cover is of finite presentation.
- `AlgebraicGeometry.isEquivalence_moduleSpecΓFunctor`: over a field `R`, every `𝒪_{Spec R}`-module
  is quasi-coherent (`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isField`), so the global
  sections functor `(Spec R).Modules ⥤ ModuleCat R` is an equivalence; in particular it is exact.
- `AlgebraicGeometry.Scheme.Modules.finrank_eq_of_coe_eq`: dimensions of global sections over `R`
  and over `Γ(Spec R, ⊤)` agree.
- `AlgebraicGeometry.Scheme.Modules.exists_presentation_isFinite` and
  `isFinitePresentation_of_finite`: over a Noetherian ring `R`, a quasi-coherent module on
  `Spec R` with finite global sections has a finite global presentation.
- `AlgebraicGeometry.Scheme.Modules.nonempty_restrict_iso_free_of_localizedModule`: a
  quasi-coherent module on `Spec R` whose global sections become free after inverting `r` is free
  on `D(r)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The image of any open of `Spec Γ(X, W)` under `fromSpec` lies in the affine open `W`. -/
lemma IsAffineOpen.fromSpec_image_le {W : X.Opens} (hW : IsAffineOpen W)
    (U : (Spec Γ(X, W)).Opens) : hW.fromSpec ''ᵁ U ≤ W :=
  (hW.fromSpec.image_le_opensRange U).trans hW.opensRange_fromSpec.le

set_option backward.isDefEq.respectTransparency false in
/-- Transporting `r ∈ Γ(X, W)` to `Γ(Spec Γ(X, W), U)` and then back along `fromSpec.appIso U`
is the restriction of `r` to `fromSpec ''ᵁ U`. -/
lemma IsAffineOpen.ΓSpecIso_inv_map_appIso_inv {W : X.Opens} (hW : IsAffineOpen W)
    (U : (Spec Γ(X, W)).Opens) :
    (Scheme.ΓSpecIso Γ(X, W)).inv ≫ (Spec Γ(X, W)).presheaf.map U.leTop.op ≫
      (hW.fromSpec.appIso U).inv =
      X.presheaf.map (homOfLE (hW.fromSpec_image_le U)).op := by
  rw [← cancel_mono (hW.fromSpec.appIso U).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Hom.appIso_hom, hW.fromSpec.naturality_assoc, hW.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Under `restrictAppIso` along `fromSpec`, the `Γ(X, W)`-action on sections of the restricted
module over `U` corresponds to the action of the restriction to `fromSpec ''ᵁ U`. -/
lemma restrictAppIso_fromSpec_smul (M : X.Modules) {W : X.Opens} (hW : IsAffineOpen W)
    {U : (Spec Γ(X, W)).Opens} (r : Γ(X, W)) (x : Γ(M.restrict hW.fromSpec, U)) :
    dsimp% (M.restrictAppIso hW.fromSpec U).hom (r • x) =
      X.presheaf.map (homOfLE (hW.fromSpec_image_le U)).op r •
        (M.restrictAppIso hW.fromSpec U).hom x := by
  rw [smul_Spec_def, smul_restrictAppIso_hom_apply, ← hW.ΓSpecIso_inv_map_appIso_inv U]
  rfl

variable (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- The restriction of a quasi-coherent module along `fromSpec` of an affine open is
localizing. -/
lemma isLocalizing_restrict_fromSpec {W : X.Opens} (hW : IsAffineOpen W) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hW.fromSpec)) :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. Every section of `M` over
`D(f)` becomes the restriction of a section over `W` after multiplication by a power of `f`. -/
lemma exists_map_eq_pow_smul_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, W)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s := by
  have hW' : W ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ X.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).le
  have hD' : X.basicOpen f ≤ hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).ge
  have := isLocalizing_restrict_fromSpec M hW f
  obtain ⟨⟨t', _, hm⟩, h⟩ := IsLocalizedModule.surj (.powers f)
    ((modulesSpecToSheaf.obj (M.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom
    ((M.restrictAppIso hW.fromSpec _).inv (M.presheaf.map (homOfLE hD).op s))
  obtain ⟨n, rfl⟩ := hm
  refine ⟨n, M.presheaf.map (homOfLE hW').op ((M.restrictAppIso hW.fromSpec ⊤).hom t'), ?_⟩
  replace h : f ^ n • (M.restrictAppIso hW.fromSpec _).inv (M.presheaf.map (homOfLE hD).op s) =
      (M.restrict hW.fromSpec).presheaf.map
        (homOfLE (le_top : (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op t' := h
  have h1 := congr(M.presheaf.map (homOfLE hD').op
    ((M.restrictAppIso hW.fromSpec (PrimeSpectrum.basicOpen f)).hom $h))
  rw [restrictAppIso_fromSpec_smul, map_smul, Iso.inv_hom_id_apply,
    map_restrictAppIso_hom_apply] at h1
  have e1 : (homOfLE hD).op ≫ (homOfLE hD').op = 𝟙 _ := Subsingleton.elim _ _
  have e2 : (homOfLE (hW.fromSpec_image_le (PrimeSpectrum.basicOpen f))).op ≫
      (homOfLE hD').op = (homOfLE (X.basicOpen_le f)).op := Subsingleton.elim _ _
  have e3 : (homOfLE (hW.fromSpec.image_mono (le_top :
      (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤))).op ≫ (homOfLE hD').op =
      (homOfLE hW').op ≫ (homOfLE (X.basicOpen_le f)).op := Subsingleton.elim _ _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply, e1, e2, e3,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, map_pow] at h1
  rw [← Functor.map_comp_apply]
  exact h1.symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. A section of `M` over `W`
whose restriction to `D(f)` vanishes is killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (t : Γ(M, W)) (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have hW' : W ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ X.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).le
  let t' := (M.restrictAppIso hW.fromSpec ⊤).inv
    (M.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op t)
  have h0 : (M.restrict hW.fromSpec).presheaf.map
      (homOfLE (le_top : (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op t' = 0 := by
    have := congr((M.restrictAppIso hW.fromSpec _).inv
      (M.presheaf.map (homOfLE hD).op $ht))
    rw [map_zero, map_zero, ← Functor.map_comp_apply] at this
    dsimp only [t']
    rw [restrictAppIso_inv_map_apply, ← Functor.map_comp_apply]
    convert this using 4
  have := isLocalizing_restrict_fromSpec M hW f
  have hz := (IsLocalizedModule.eq_zero_iff (.powers f)
    ((modulesSpecToSheaf.obj (M.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom (m := t')).mp
  obtain ⟨⟨_, hm⟩, hn⟩ := hz h0
  obtain ⟨n, rfl⟩ := hm
  refine ⟨n, ?_⟩
  rw [Submonoid.smul_def] at hn
  have := congr(M.presheaf.map (homOfLE hW').op ((M.restrictAppIso hW.fromSpec ⊤).hom $hn))
  rw [restrictAppIso_fromSpec_smul, map_zero, map_zero, map_smul, Iso.inv_hom_id_apply] at this
  have hid : (homOfLE (hW.fromSpec_image_le ⊤)).op ≫ (homOfLE hW').op =
      𝟙 (Opposite.op W) := Subsingleton.elim _ _
  simp only [← Functor.map_comp_apply, hid, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] at this
  exact this

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Opposite

variable {X : Scheme.{u}}

/-- Let `M` be a quasi-coherent `𝒪_X`-module, `U` an affine open and `g ∈ Γ(X, U)`. Then the
restriction map `Γ(M, U) → Γ(M, D(g))` is a localization at the powers of `g`, the
`Γ(X, U)`-module structure on `Γ(M, D(g))` being restriction of scalars along
`Γ(X, U) → Γ(X, D(g))`. -/
lemma isLocalizedModule_basicOpen (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
    IsLocalizedModule.Away g
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le g)).op
        map_add' := map_add _
        map_smul' := map_smul M _ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) } := by
  let : Module Γ(X, U) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := hx
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n)) := by
      rw [map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b hab ↦ ?_, fun m ↦ ⟨hu.unit⁻¹ • m, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at hab
      exact hu.smul_left_cancel.mp hab
    · rw [Module.algebraMap_end_apply]
      exact smul_inv_smul hu.unit m
  · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen M hU g y
    rw [← map_pow] at ht
    exact ⟨⟨t, ⟨g ^ n, n, rfl⟩⟩, ht.symm⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M hU g (x₁ - x₂)
      ((map_sub _ x₁ x₂).trans (sub_eq_zero.mpr h))
    exact ⟨⟨g ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Conversely to `exists_map_eq_pow_smul_of_isAffineOpen` and
`exists_pow_smul_eq_zero_of_isAffineOpen`, let `W` be an affine open such that for every
`f ∈ Γ(X, W)` every section of `M` over `D(f)` becomes the restriction of a section over `W` after
multiplication by a power of `f`, and every section over `W` vanishing on `D(f)` is killed by a
power of `f`. Then the restriction of `M` along `fromSpec` is localizing. -/
lemma isLocalizing_restrict_fromSpec_of_forall (M : X.Modules) {W : X.Opens}
    (hW : IsAffineOpen W)
    (h₁ : ∀ (f : Γ(X, W)) (s : Γ(M, X.basicOpen f)), ∃ (n : ℕ) (t : Γ(M, W)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s)
    (h₂ : ∀ (f : Γ(X, W)) (t : Γ(M, W)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
      ∃ n : ℕ, f ^ n • t = 0) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hW.fromSpec)) := by
  intro f
  have hW' : W ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ X.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).le
  have hD' : X.basicOpen f ≤ hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).ge
  have hinj : Function.Injective (M.presheaf.map (homOfLE hD').op) := fun a b hab ↦ by
    have := congr(M.presheaf.map (homOfLE hD).op $hab)
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      show (homOfLE hD').op ≫ (homOfLE hD).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
      ConcreteCategory.id_apply] at this
  have hhom (U : (Spec Γ(X, W)).Opens) :
      Function.Injective (M.restrictAppIso hW.fromSpec U).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_end_of_le_basicOpen f le_rfl) (fun x ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨n, t, ht⟩ := h₁ f
      (M.presheaf.map (homOfLE hD').op ((M.restrictAppIso hW.fromSpec _).hom x))
    let y := (M.restrictAppIso hW.fromSpec ⊤).inv
      (M.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op t)
    have key : M.presheaf.map (homOfLE hD').op ((M.restrictAppIso hW.fromSpec _).hom (f ^ n • x)) =
        M.presheaf.map (homOfLE hD').op ((M.restrictAppIso hW.fromSpec _).hom
          ((M.restrict hW.fromSpec).presheaf.map (homOfLE (le_top :
            (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op y)) := by
      rw [restrictAppIso_fromSpec_smul, map_smul, map_restrictAppIso_hom_apply]
      dsimp only [y]
      rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, Subsingleton.elim (_ ≫ _ ≫ _) (homOfLE (X.basicOpen_le f)).op,
        ht, Subsingleton.elim (_ ≫ _) (homOfLE (X.basicOpen_le f)).op, map_pow]
    exact ⟨n, y, hhom _ (hinj key)⟩
  · replace ht : (M.restrict hW.fromSpec).presheaf.map (homOfLE (le_top :
        (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op t = 0 := ht
    let t' := M.presheaf.map (homOfLE hW').op ((M.restrictAppIso hW.fromSpec ⊤).hom t)
    have ht' : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t' = 0 := by
      have := congr(M.presheaf.map (homOfLE hD').op ((M.restrictAppIso hW.fromSpec _).hom $ht))
      rw [map_restrictAppIso_hom_apply, map_zero, map_zero, ← Functor.map_comp_apply] at this
      dsimp only [t']
      rw [← Functor.map_comp_apply]
      exact (congrArg (fun φ ↦ M.presheaf.map φ _) (Subsingleton.elim _ _)).trans this
    obtain ⟨n, hn⟩ := h₂ f t' ht'
    refine ⟨n, hhom _ ?_⟩
    have ht : (M.restrictAppIso hW.fromSpec ⊤).hom t =
        M.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op t' := by
      dsimp only [t']
      rw [← Functor.map_comp_apply, Subsingleton.elim (_ ≫ _) (𝟙 _),
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    rw [restrictAppIso_fromSpec_smul, map_zero, ht, ← map_smul, hn, map_zero]

/-- The sections of an invertible `𝒪_X`-module over an affine open `U` form a flat
`Γ(X, U)`-module. -/
lemma flat_sections_of_isInvertible (M : X.Modules) [M.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Flat Γ(X, U) Γ(M, U) := by
  let s : Set Γ(X, U) := {g | ∃ Y : X.Opens, X.basicOpen g ≤ Y ∧
    Nonempty (M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y))}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨Y, hxY, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
    obtain ⟨g, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, Y, hgY, ⟨e⟩⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(M, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen M hU r.1
  refine Module.flat_of_isLocalized_span Γ(X, U) Γ(M, U) s hs
    (fun r ↦ Γ(M, X.basicOpen r.1)) (fun r ↦
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul M _ }) fun r ↦ ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := r.2
  have := Module.Flat.of_linearEquiv (sectionsLinearEquivOfOverIsoUnit e hY)
  have := hU.isLocalization_basicOpen r.1
  have := IsLocalization.flat Γ(X, X.basicOpen r.1) (.powers r.1)
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Limits

/-- The restriction of a module of finite presentation along an open immersion is of finite
presentation. This is the finite-presentation analogue of
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`. -/
instance isFinitePresentation_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFinitePresentation] :
    ((restrictFunctor f).obj M).IsFinitePresentation := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  have hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    f.opensFunctor φ (Scheme.Modules.restrictUnitIso _)

/-- A presentation of the restriction `M.restrict U.ι` of an `𝒪_X`-module `M` to an open `U`
gives a presentation of `M.over U`, transported along `AlgebraicGeometry.Scheme.Modules.overEquiv`.
-/
noncomputable def presentationOverOfRestrict {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation :=
  letI F : SheafOfModules.{u} U.toScheme.ringCatSheaf ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over U) := (overEquiv U).inverse
  haveI : PreservesColimitsOfSize.{u, u} F :=
    (overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  letI e : F.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  (P.map F (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso e.hom

instance {X : Scheme.{u}} {M : X.Modules} (U : X.Opens) (P : (M.restrict U.ι).Presentation)
    [P.IsFinite] : (presentationOverOfRestrict U P).IsFinite where
  isFiniteType_generators := ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_generators
    (p := P)).finite⟩
  isFiniteType_relations := ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_relations
    (p := P)).finite⟩

/-- An `𝒪_X`-module whose restrictions to the members of an open cover have finite global
presentations is of finite presentation. -/
theorem isFinitePresentation_of_isOpenCover {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    {U : ι → X.Opens} (hU : IsOpenCover U) (P : ∀ i, (M.restrict (U i).ι).Presentation)
    [∀ i, (P i).IsFinite] : M.IsFinitePresentation := by
  let σ : SheafOfModules.QuasicoherentData.{u, u, u, u} M :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      presentation i := presentationOverOfRestrict (U i) (P i) }
  have : σ.IsFinitePresentation :=
    { isFinite_presentation i := inferInstanceAs (presentationOverOfRestrict (U i) (P i)).IsFinite }
  exact σ.isFinitePresentation

/-- A presentation of the restriction of `M` along an open immersion `f` gives a presentation
of the restriction of `M` to the open subscheme `f.opensRange`. -/
noncomputable def presentationRestrictOpensRange {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (P : (M.restrict f).Presentation) :
    (M.restrict f.opensRange.ι).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (((restrictFunctorComp f.isoOpensRange.inv f).app M).inv ≫
      (restrictFunctorCongr f.isoOpensRange_inv_comp).hom.app M)
    (presentationRestrict f.isoOpensRange.inv P)

instance {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {M : X.Modules}
    (P : (M.restrict f).Presentation) [P.IsFinite] :
    (presentationRestrictOpensRange f P).IsFinite where
  isFiniteType_generators := ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_generators
    (p := P)).finite⟩
  isFiniteType_relations := ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_relations
    (p := P)).finite⟩

/-- An `𝒪_X`-module whose restrictions along a family of open immersions covering `X` have
finite global presentations is of finite presentation. -/
theorem isFinitePresentation_of_iSup_opensRange_eq_top {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (P : ∀ i, (M.restrict (f i)).Presentation)
    [∀ i, (P i).IsFinite] : M.IsFinitePresentation :=
  isFinitePresentation_of_isOpenCover M (U := fun i ↦ (f i).opensRange) hf
    (fun i ↦ presentationRestrictOpensRange (f i) (P i))

/-- **The pullback of a quasi-coherent module is quasi-coherent.** For `g : X ⟶ Y` and a
quasi-coherent `𝒪_Y`-module `M`, take presentations of `M` over the members `U i` of an open cover
of `Y`. Pulling them back along the restrictions `g ∣_ U i`, which preserve colimits and the
structure sheaf, gives presentations of `g^* M` over the open cover `g ⁻¹ᵁ U i` of `X`. -/
instance isQuasicoherent_pullback {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] : ((Modules.pullback g).obj M).IsQuasicoherent := by
  obtain ⟨ι, U, pres, hU, -⟩ := M.exists_isOpenCover_presentation
  have (i : ι) : PreservesColimitsOfSize.{u, u} (Modules.pullback (g ∣_ U i)) := inferInstance
  let P (i : ι) : (((Modules.pullback g).obj M).restrict (g ⁻¹ᵁ U i).ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((restrictFunctorIsoPullback _).app _ ≪≫ (Modules.pullbackComp (g ⁻¹ᵁ U i).ι g).app M ≪≫
        (Modules.pullbackCongr (morphismRestrict_ι g (U i)).symm).app M ≪≫
        ((Modules.pullbackComp (g ∣_ U i) (U i).ι).symm).app M ≪≫
        (Modules.pullback (g ∣_ U i)).mapIso ((restrictFunctorIsoPullback _).app M).symm).inv
      ((pres i).map (Modules.pullback (g ∣_ U i)) (pullbackObjUnitIso _).symm)
  let σ : SheafOfModules.QuasicoherentData.{u, u, u, u} ((Modules.pullback g).obj M) :=
    { I := ι
      X := fun i ↦ g ⁻¹ᵁ U i
      coversTop := by
        rw [Opens.coversTop_iff]
        refine IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
        obtain ⟨i, hi⟩ := hU.exists_mem (g.base x)
        exact Opens.mem_iSup.mpr ⟨i, hi⟩
      presentation i := presentationOverOfRestrict (g ⁻¹ᵁ U i) (P i) }
  exact σ.isQuasicoherent

/-- If the global sections of an `𝒪_{Spec R}`-module are finite over `Γ(Spec R, ⊤)`, they are
finite over `R`. -/
theorem finite_sections_top_of_finite {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤)] : Module.Finite R Γ(M, ⊤) := by
  have : Module.Finite R Γ(Spec R, ⊤) := by
    refine Module.Finite.of_surjective (Algebra.linearMap R Γ(Spec R, ⊤)) fun x ↦ ?_
    exact ⟨(Scheme.ΓSpecIso R).hom x, by simp⟩
  exact Module.Finite.trans Γ(Spec R, ⊤) Γ(M, ⊤)

/-- A quasi-coherent module on the spectrum of a Noetherian ring `R` whose global sections are a
finite `R`-module has a finite global presentation: it is `M^~` for the finitely presented
`R`-module `M` of its global sections. -/
theorem exists_presentation_isFinite {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Module.Finite R Γ(M, ⊤)] :
    ∃ P : M.Presentation, P.IsFinite := by
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  have : Module.Finite R N := ‹Module.Finite R Γ(M, ⊤)›
  obtain ⟨s, hs, t, ht⟩ := (Module.finitePresentation_of_finite R N).out
  have : IsIso (C := SheafOfModules.{u} (Spec R).ringCatSheaf) M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨(presentationTilde N (s : Set N) hs (t : Set _) ht).ofIsIso M.fromTildeΓ,
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set N))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }⟩

/-- A quasi-coherent module on the spectrum of a Noetherian ring `R` whose global sections are a
finite `R`-module is of finite presentation. -/
theorem isFinitePresentation_of_finite {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Module.Finite R Γ(M, ⊤)] :
    M.IsFinitePresentation := by
  obtain ⟨P, _⟩ := exists_presentation_isFinite M
  exact P.isFinitePresentation

open Opposite in
/-- **A quasi-coherent module which is free after inverting `r` is free on `D(r)`.** Let `M` be a
quasi-coherent module on `Spec R` and `r ∈ R` such that the localization `Γ(M, ⊤)_r` is a free
`R_r`-module with basis indexed by `ι`. Then the restriction of `M` to the basic open
`D(r) = Spec R_r` is the free module on `ι`: it is `Γ(M, D(r))^~`, and `Γ(M, D(r)) = Γ(M, ⊤)_r`
since `M` is quasi-coherent. -/
theorem nonempty_restrict_iso_free_of_localizedModule {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) {ι : Type u}
    (e : LocalizedModule.Away r Γ(M, ⊤) ≃ₗ[Localization.Away r] (ι →₀ Localization.Away r)) :
    Nonempty (M.restrict (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≅
      SheafOfModules.free ι) := by
  let S : CommRingCat.{u} := .of (Localization.Away r)
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let j := Spec.map φ
  let N := M.restrict j
  have hU : j ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
    rw [Hom.image_top_eq_opensRange, Hom.opensRange_localizationAway]
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  have key : ∀ U : (Spec R).Opens, U = PrimeSpectrum.basicOpen r →
      IsLocalizedModule (.powers r)
        ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top : U ⟶ ⊤).op).hom := by
    rintro U rfl
    exact hloc r
  let X : ModuleCat S := (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)
  let : Module (Localization.Away r) X := X.isModule
  let : Module R X := Module.compHom X φ.hom
  have : IsScalarTower R (Localization.Away r) X := ⟨fun a s x ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let ι₀ : Γ(M, j ''ᵁ ⊤) ≃ₗ[R] X :=
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' a x := (restrictAppIso_smul_Spec (M := M) φ a (x : Γ(N, ⊤))).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  let ρ := ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top : j ''ᵁ ⊤ ⟶ ⊤).op).hom
  have : IsLocalizedModule (.powers r) (ι₀.toLinearMap ∘ₗ ρ) :=
    IsLocalizedModule.of_linearEquiv (.powers r) _ ι₀ (hf := key _ hU)
  let e₁ := IsLocalizedModule.iso (.powers r) (ι₀.toLinearMap ∘ₗ ρ)
  let e₂ := e₁.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
  let e₃ : X ≃ₗ[S] (ι →₀ S) := e₂.symm ≪≫ₗ e
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor j M
  have : IsIso (fromTildeΓ (R := S) N) := isIso_fromTildeΓ_of_isQuasicoherent (R := S) N
  let i₁ : N ≅ tilde X := (asIso (fromTildeΓ (R := S) N)).symm
  exact ⟨i₁ ≪≫ (tilde.functor S).mapIso (show X ≅ ModuleCat.of S (ι →₀ S) from e₃.toModuleIso) ≪≫
    tildeFinsupp ι⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

open CategoryTheory Limits Opposite

/-- Over a field `R`, every sheaf of `R`-modules on `Spec R` coming from an `𝒪_{Spec R}`-module is
localizing: a basic open `D(f)` is empty for `f = 0` and everything for `f ≠ 0`. -/
theorem isLocalizing_of_isField (hR : IsField R) (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) := by
  let := hR.toField
  intro f
  by_cases hf : f = 0
  · subst hf
    have : Subsingleton ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen 0))) :=
      ModuleCat.subsingleton_of_isZero (IsTerminal.isZero
        ((modulesSpecToSheaf.obj M).isTerminalOfEqEmpty PrimeSpectrum.basicOpen_zero))
    exact
      { map_units _ := isUnit_of_subsingleton _
        surj _ := ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
        exists_of_eq {x₁ x₂} _ := ⟨⟨0, 1, pow_one _⟩, by
          change (0 : R) • x₁ = (0 : R) • x₂
          simp⟩ }
  · have hf' : IsUnit f := Ne.isUnit hf
    have hU : ⊤ ≤ PrimeSpectrum.basicOpen f := fun x _ ↦ (PrimeSpectrum.mem_basicOpen _ _).2
      fun h ↦ x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hf')
    have hb := TopCat.Presheaf.bijective_map_of_eq (modulesSpecToSheaf.obj M).obj
      (PrimeSpectrum.basicOpen f).leTop.op (hU.antisymm le_top)
    exact
      { map_units x := by
          obtain ⟨_, n, rfl⟩ := x
          exact (hf'.pow n).map _
        surj y := by
          obtain ⟨x, rfl⟩ := hb.2 y
          exact ⟨⟨x, 1⟩, by simp⟩
        exists_of_eq h := ⟨1, by simpa using hb.1 h⟩ }

/-- Over a field `R`, every `𝒪_{Spec R}`-module is quasi-coherent: it is `Γ(M)^~`. -/
theorem Scheme.Modules.isIso_fromTildeΓ_of_isField (hR : IsField R) (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing M).2 (isLocalizing_of_isField hR M)

instance : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  (tilde.adjunction (R := R)).isRightAdjoint

instance : (moduleSpecΓFunctor (R := R)).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryProducts (moduleSpecΓFunctor (R := R))
  Functor.additive_of_preservesBinaryBiproducts _

/-- Over a field `R`, the global sections functor `(Spec R).Modules ⥤ ModuleCat R` is an
equivalence, with inverse `M ↦ M^~`. In particular it is exact. -/
theorem isEquivalence_moduleSpecΓFunctor (hR : IsField R) :
    (moduleSpecΓFunctor (R := R)).IsEquivalence := by
  have (M : (Spec R).Modules) : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isField hR M
  have (M : ModuleCat R) : IsIso ((tilde.adjunction (R := R)).unit.app M) :=
    inferInstanceAs (IsIso ((tilde.toTildeΓNatIso (R := R)).hom.app M))
  exact (tilde.adjunction (R := R)).toEquivalence.isEquivalence_inverse

namespace Scheme.Modules

/-- On global sections of an `𝒪_{Spec R}`-module, `r ∈ R` acts as its image in `Γ(Spec R, ⊤)`. -/
lemma smul_top_eq (M : (Spec R).Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = (Scheme.ΓSpecIso R).inv r • x := by
  rw [smul_Spec_def]
  congr 1

/-- A set of global sections of an `𝒪_{Spec R}`-module which is a submodule both over `R` and over
`Γ(Spec R, ⊤)` has the same dimension over both. -/
theorem finrank_eq_of_coe_eq (M : (Spec R).Modules) (p : Submodule R Γ(M, ⊤))
    (p' : Submodule Γ(Spec R, ⊤) Γ(M, ⊤)) (h : (p : Set Γ(M, ⊤)) = p') :
    Module.finrank R p = Module.finrank Γ(Spec R, ⊤) p' := by
  let j : p ≃+ p' := { Set.equivOfEq h with map_add' _ _ := rfl }
  have hi : Function.Bijective (Scheme.ΓSpecIso R).inv :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  exact congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv _ j hi fun r x ↦ Subtype.ext (smul_top_eq M r x))

end Scheme.Modules

section AssociatedSections

open TensorProduct

variable {A B : CommRingCat.{u}} [Algebra A B] (M : Type u) [AddCommGroup M] [Module B M]
  [Module A M] [IsScalarTower A B M]

/-- **Sections of an associated sheaf over a localization.** Let `A → B` be a ring map, `M` a
`B`-module and `a ∈ A`. The open subscheme `Spec (B ⊗_A A_a)` of `Spec B` is the basic open
`D(a)`, and the sections of the associated quasi-coherent sheaf `M~` over it are canonically
`A`-linearly isomorphic to `A_a ⊗_A M`, compatibly with `m ↦ 1 ⊗ m`
(`tildeSectionsBasicOpenTensorEquiv_apply`).

(blueprint: `pqf-lem-associated-sections-localize`) -/
noncomputable def tildeSectionsBasicOpenTensorEquiv (a : A) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((modulesSpecToSheaf.obj (tilde (ModuleCat.of B M))).presheaf.obj
          (.op (PrimeSpectrum.basicOpen (algebraMap A B a)))) ≃ₗ[A]
      Localization.Away a ⊗[A] M :=
  let N := (modulesSpecToSheaf.obj (tilde (ModuleCat.of B M))).presheaf.obj
    (.op (PrimeSpectrum.basicOpen (algebraMap A B a)))
  letI : Module A N := Module.compHom N (algebraMap A B)
  haveI : IsScalarTower A B N := ⟨fun x y z ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let φ := (tilde.toOpen (ModuleCat.of B M) (PrimeSpectrum.basicOpen (algebraMap A B a))).hom
  haveI : IsLocalizedModule (.powers (algebraMap A B a)) φ :=
    (fun (P : ModuleCat B) (b : B) ↦ (inferInstance : IsLocalizedModule (.powers b)
      (tilde.toOpen P (PrimeSpectrum.basicOpen b)).hom)) (ModuleCat.of B M) _
  haveI := IsLocalizedModule.restrictScalars_powers a φ
  IsLocalizedModule.linearEquiv (.powers a) (φ.restrictScalars A)
    (TensorProduct.mk A (Localization.Away a) M 1)

@[simp]
theorem tildeSectionsBasicOpenTensorEquiv_apply (a : A) (m : M) :
    tildeSectionsBasicOpenTensorEquiv M a ((tilde.toOpen (ModuleCat.of B M)
      (PrimeSpectrum.basicOpen (algebraMap A B a))).hom m) = 1 ⊗ₜ m := by
  let N := (modulesSpecToSheaf.obj (tilde (ModuleCat.of B M))).presheaf.obj
    (.op (PrimeSpectrum.basicOpen (algebraMap A B a)))
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B N := ⟨fun x y z ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let φ := (tilde.toOpen (ModuleCat.of B M) (PrimeSpectrum.basicOpen (algebraMap A B a))).hom
  have : IsLocalizedModule (.powers (algebraMap A B a)) φ :=
    (fun (P : ModuleCat B) (b : B) ↦ (inferInstance : IsLocalizedModule (.powers b)
      (tilde.toOpen P (PrimeSpectrum.basicOpen b)).hom)) (ModuleCat.of B M) _
  have := IsLocalizedModule.restrictScalars_powers a φ
  exact IsLocalizedModule.linearEquiv_apply _ _ _ m

end AssociatedSections

end AlgebraicGeometry
