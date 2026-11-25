/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Nilpotence of the vanishing ideal on a coherent module

Source: Stacks Project, Tag 01Y9.
(blueprint: lem-pc-s3-coherent-support-vanishing-ideal-nilpotence)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem ideal_qc {X : Scheme.{u}} (J : X.IdealSheafData)
    (K : X.Modules) (e : K ≅ J.toModules) :
    K.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated J.subschemeι _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (isQuasicoherent_kernel J.toPushforwardSubscheme)

open MonoidalCategory in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem multiplication_range {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [M.IsQuasicoherent]
    [(MonoidalCategory.tensorObj K M).IsQuasicoherent] (U : X.affineOpens)
    (ht : Function.Surjective (tensorSectionsMap K M U.1)) :
    let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
    Set.range ((idealModuleProductι i M).app U.1) =
      {s | s ∈ I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))} := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := i ▷ M ≫ (λ_ M).hom
  let I : Ideal Γ(X, U.1) := LinearMap.range (i.val.app (op U.1)).hom
  have hp (s : Γ(K, U.1)) (t : Γ(M, U.1)) :
      a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) = (show Γ(X, U.1) from i.app U.1 s) • t := by
    rw [tensorSectionsMap_tmul]
    change (λ_ M).hom.app U.1 ((i ▷ M).app U.1 (tmulSection s t)) = _
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
    rfl
  have ha : LinearMap.range (a.val.app (op U.1)).hom = I • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht z
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        change a.app U.1 (tensorSectionsMap K M U.1 (s ⊗ₜ t)) ∈ I • ⊤
        rw [hp]
        exact Submodule.smul_mem_smul ⟨s, rfl⟩ (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := hr
      exact ⟨tensorSectionsMap K M U.1 (s ⊗ₜ t), hp s t⟩
  have hb := (quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
  have hi : Set.range ((idealModuleProductι i M).app U.1) =
      Set.range ((Abelian.image.ι a).app U.1) := by
    let e := Abelian.imageIsoImage a
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.inv.app U.1 t, ?_⟩
      have h : e.inv ≫ Abelian.image.ι a = image.ι a := by
        calc
          _ = e.inv ≫ e.hom ≫ image.ι a :=
            congrArg (fun f ↦ e.inv ≫ f)
              (Abelian.imageIsoImage_hom_comp_image_ι a).symm
          _ = _ := by simp
      exact congrArg (fun f ↦ f.app U.1 t) h
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.app U.1 t, ?_⟩
      exact congrArg (fun f ↦ f.app U.1 t)
        (Abelian.imageIsoImage_hom_comp_image_ι a)
  rw [hi, hb.1]
  exact congrArg (fun P : Submodule Γ(X, U.1) Γ(M, U.1) ↦ (P : Set Γ(M, U.1))) ha


set_option backward.isDefEq.respectTransparency false in
private theorem powers_affine_sections {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent] :
    ∀ n : ℕ, (idealSheafPower i n).1.IsQuasicoherent ∧
      ∀ U : X.affineOpens,
        (LinearMap.range ((idealSheafPower i n).2.val.app (op U.1)).hom :
          Ideal Γ(X, U.1)) =
          (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) ^ n := by
  have hqc (n : ℕ) : (idealSheafPower i n).1.IsQuasicoherent := by
    induction n using Nat.twoStepInduction with
    | zero => exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    | one => assumption
    | more n _ ih =>
      let M := (idealSheafPower i (n + 1)).1
      have : M.IsQuasicoherent := ih
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      let a := MonoidalCategory.whiskerRight i M ≫ (MonoidalCategory.leftUnitor M).hom
      have := (quasiCoherent_tensor_product_affine_sections K M).1
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (Abelian.imageIsoImage a)
        (quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.1
  intro n
  refine ⟨hqc n, ?_⟩
  intro U
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    apply LinearMap.range_eq_top.mpr
    exact fun a ↦ ⟨a, rfl⟩
  | one => simp [idealSheafPower]
  | more n _ ih =>
    let M := (idealSheafPower i (n + 1)).1
    have : M.IsQuasicoherent := hqc (n + 1)
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have := (quasiCoherent_tensor_product_affine_sections K M).1
    have hprod : LinearMap.range ((idealModuleProductι i M).val.app (op U.1)).hom =
        (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) •
          (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
      apply SetLike.coe_injective
      exact multiplication_range i M U
        ((quasiCoherent_tensor_product_affine_sections K M).2 U.1 U.2).2
    change LinearMap.range
      (((idealSheafPower i (n + 1)).2.val.app (op U.1)).hom.comp
        ((idealModuleProductι i M).val.app (op U.1)).hom) = _
    rw [LinearMap.range_comp, hprod, Submodule.map_smul'', Submodule.map_top, ih,
      Ideal.smul_eq_mul]
    exact (pow_succ'
      (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) (n + 1)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem affine_source_zero_of_sections {X Y : Scheme.{u}} (H : X.Modules)
    [H.IsQuasicoherent] (j : Y ⟶ X) [IsOpenImmersion j] [IsAffine Y]
    [Subsingleton Γ(H, j ''ᵁ ⊤)] : IsZero (H.restrict j) := by
  let U : X.affineOpens := ⟨j ''ᵁ ⊤, (isAffineOpen_top Y).image_of_isOpenImmersion j⟩
  let N := H.restrict U.2.fromSpec
  have : N.IsQuasicoherent := Modules.isQuasicoherent_restrictFunctor _ H
  have hi : U.2.fromSpec ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  have : Subsingleton Γ(N, ⊤) := by
    have : Subsingleton Γ(H, U.2.fromSpec ''ᵁ ⊤) := hi.symm ▸ inferInstance
    exact (H.restrictAppIso U.2.fromSpec ⊤).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  have hz : IsZero N := by
    have : Subsingleton ((moduleSpecΓFunctor (R := Γ(X, U.1))).obj N) :=
      (inferInstance : Subsingleton Γ(N, ⊤))
    have : IsIso N.fromTildeΓ := Modules.isIso_fromTildeΓ_of_isQuasicoherent N
    have hz := (tilde.functor Γ(X, U.1)).map_isZero
      (ModuleCat.isZero_of_subsingleton ((moduleSpecΓFunctor (R := Γ(X, U.1))).obj N))
    exact hz.of_iso (asIso N.fromTildeΓ).symm
  have hsec (V : X.Opens) (hV : V ≤ U.1) : Subsingleton Γ(H, V) := by
    have : Subsingleton Γ(N, U.2.fromSpec ⁻¹ᵁ V) := ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation _ (Opposite.op (U.2.fromSpec ⁻¹ᵁ V))).map_isZero hz)
    have hv : U.2.fromSpec ''ᵁ (U.2.fromSpec ⁻¹ᵁ V) = V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, U.2.opensRange_fromSpec,
        inf_eq_right.mpr hV]
    have hs : Subsingleton Γ(H, U.2.fromSpec ''ᵁ (U.2.fromSpec ⁻¹ᵁ V)) :=
      (H.restrictAppIso U.2.fromSpec _).addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
    exact hv ▸ hs
  refine (IsZero.iff_id_eq_zero _).mpr (Modules.hom_ext _ _ fun V ↦ ?_)
  have : Subsingleton Γ(H, j ''ᵁ V) :=
    hsec _ (by simpa [U, Scheme.Hom.image_top_eq_opensRange] using
      j.image_le_opensRange V)
  have : Subsingleton Γ(H.restrict j, V) :=
    (H.restrictAppIso j V).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  ext a
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem powerProduct_isZero_iff_affine_cover (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) [K.IsQuasicoherent]
    (S : Set X.affineOpens) (hS : ∀ x : X, ∃ U ∈ S, x ∈ U.1) (t : ℕ) :
    IsZero (idealModuleProduct (idealSheafPower i t).2 F) ↔
      ∀ U ∈ S, (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) ^ t ≤
        Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  let J := (idealSheafPower i t).1
  let ι : J ⟶ SheafOfModules.unit X.ringCatSheaf := (idealSheafPower i t).2
  have hj : J.IsQuasicoherent := (powers_affine_sections i t).1
  let φ : MonoidalCategory.tensorObj J F ⟶ F :=
    MonoidalCategory.whiskerRight ι F ≫ (MonoidalCategory.leftUnitor F).hom
  have ht : (MonoidalCategory.tensorObj J F).IsQuasicoherent :=
    (Modules.quasiCoherent_tensor_product_affine_sections J F).1
  have him := Modules.quasiCoherent_cokernel_image φ
  have hq : (Abelian.image φ).IsQuasicoherent := him.2.2.2.2.2.2.2.1
  have hp (U : X.affineOpens) :
      Set.range (ι.app U.1) =
        {a | a ∈ (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) ^ t} := by
    exact congrArg (fun I : Ideal Γ(X, U.1) ↦ (I : Set Γ(X, U.1)))
      ((powers_affine_sections i t).2 U)
  have hm (U : X.Opens) (a : Γ(J, U)) (s : Γ(F, U)) :
      φ.app U (Modules.tmulSection a s) = (show Γ(X, U) from ι.app U a) • s := by
    change (MonoidalCategory.leftUnitor F).hom.app U
      ((MonoidalCategory.whiskerRight ι F).app U (Modules.tmulSection a s)) = _
    rw [Modules.whiskerRight_app_tmulSection, Modules.leftUnitor_hom_app_tmulSection']
    rfl
  change IsZero (image φ) ↔ _
  constructor
  · intro hz U hU a ha
    obtain ⟨b, hb⟩ := (Set.ext_iff.mp (hp U) a).mpr ha
    apply Module.mem_annihilator.mpr
    intro s
    have he : φ = 0 := eq_zero_of_image_eq_zero (hz.eq_of_src _ _)
    have hh := congrArg
      (fun f : MonoidalCategory.tensorObj J F ⟶ F ↦ f.app U.1 (Modules.tmulSection b s)) he
    rw [hm, hb] at hh
    simpa using hh
  · intro h
    have hs (U : S) : Subsingleton Γ(Abelian.image φ, U.1.1) := by
      have hz : ∀ z : Γ(MonoidalCategory.tensorObj J F, U.1.1), φ.app U.1.1 z = 0 := by
        intro z
        obtain ⟨w, rfl⟩ :=
          (Modules.quasiCoherent_tensor_product_affine_sections J F).2 _ U.1.2 |>.2 z
        induction w using TensorProduct.inductionOn with
        | tmul a s =>
          rw [Modules.tensorSectionsMap_tmul, hm]
          exact Module.mem_annihilator.mp (h U.1 U.2
            ((Set.ext_iff.mp (hp U.1) _).mp ⟨a, rfl⟩)) s
        | add a b ha hb => simp only [map_add, ha, hb, add_zero]
      have hinj : Function.Injective ((Abelian.image.ι φ).app U.1.1) := by
        exact (ModuleCat.mono_iff_injective _).mp
          ((SheafOfModules.evaluation _ (Opposite.op U.1.1)).map_mono _)
      refine ⟨fun a b ↦ hinj ?_⟩
      have hr := (him.2.2.2.2.2.2.2.2 U.1).1
      have hh (a : Γ(Abelian.image φ, U.1.1)) :
          (Abelian.image.ι φ).app U.1.1 a = 0 := by
        obtain ⟨z, he⟩ := (Set.ext_iff.mp hr _).mp ⟨a, rfl⟩
        exact he.symm.trans (hz z)
      rw [hh, hh]
    have hc : (⨆ U : S, U.1.1) = ⊤ := by
      apply top_unique
      intro x hx
      obtain ⟨U, hU, hxU⟩ := hS x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
    have hz : IsZero (Abelian.image φ) := Modules.isZero_of_iSup_eq_top _
      (fun U : S ↦ U.1.1) hc (fun U ↦ by
        have : Subsingleton Γ(Abelian.image φ, U.1.1.ι ''ᵁ ⊤) := by
          simpa using hs U
        exact affine_source_zero_of_sections (Abelian.image φ) U.1.1.ι)
    exact hz.of_iso (Abelian.imageIsoImage φ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The vanishing ideal of a closed set containing the support kills a coherent module
by some power.

Source: Stacks Project, Tag 01Y9, as used in the ideal-power paragraph of Tag 01YF.
(blueprint: lem-pc-s3-coherent-support-vanishing-ideal-nilpotence)

Proof: On every affine open of the Noetherian scheme the coherent module has a finite
module of sections M. Its support is V(Ann M). The vanishing ideal J of T has zero
locus T on that affine. Support containment implies J is contained in the radical
of Ann M. Since J is finitely generated, a power of J is contained in Ann M.
Take a finite affine cover and the maximum of these exponents. Every higher power
also annihilates the corresponding affine section module. The ideal-product
construction has affine sections equal to the product of the section ideal and
module, so the resulting global power product is zero on the cover, hence zero
by the sheaf axiom. An empty scheme admits exponent zero. -/
theorem coherent_support_vanishingIdeal_nilpotence
    (X : Scheme.{u}) [IsNoetherian X] (T : TopologicalSpace.Closeds X)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ (T : Set X)) :
    ∃ n : ℕ, IsZero (idealModuleProduct
      (idealSheafPower (IdealSheafData.vanishingIdeal T).toModulesι n).2 F) := by
  let K := IdealSheafData.vanishingIdeal T
  classical
  obtain ⟨hq, ht⟩ :=
    (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  obtain ⟨S, hfin, hcover⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨isCompact_univ (X := X), isOpen_univ⟩
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U.1 := by
    intro x
    have hx : x ∈ ⋃ U ∈ S, (U.1 : Set X) := by rw [← hcover]; trivial
    obtain ⟨U, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hU, hx⟩ := Set.mem_iUnion.mp hx
    exact ⟨U, hU, hx⟩
  have hsupp := (Modules.finite_type_module_support_closed X F).2.2.1
  have hzero := (quasi_coherent_ideal_zero_set_affine X K).2.2.1
  have hloc :
      ({x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
        {x : X | ¬ Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom}) ↔
      ∀ U ∈ S, K.ideal U ≤ (Module.annihilator Γ(X, U.1) Γ(F, U.1)).radical := by
    constructor
    · intro h U _
      apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      intro p hp
      have hx : U.2.fromSpec p ∈
          {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) := by
        rw [hsupp U]
        exact ⟨p, hp, rfl⟩
      have hy : U.2.fromSpec p ∈
          {x : X | ¬ Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩
              (U.1 : Set X) := ⟨h hx.1, hx.2⟩
      rw [hzero U] at hy
      obtain ⟨q, hq, heq⟩ := hy
      have he : q = p := U.2.fromSpec.isOpenEmbedding.injective heq
      exact he ▸ hq
    · intro h x hx
      obtain ⟨U, hU, hxU⟩ := hS x
      have hx' : x ∈ U.2.fromSpec '' PrimeSpectrum.zeroLocus
          (Module.annihilator Γ(X, U.1) Γ(F, U.1) : Set Γ(X, U.1)) := by
        rw [← hsupp U]
        exact ⟨hx, hxU⟩
      obtain ⟨p, hp, rfl⟩ := hx'
      have hp' := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mpr (h U hU) hp
      have hy : U.2.fromSpec p ∈
          {x : X | ¬ Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩
              (U.1 : Set X) := by
        rw [hzero U]
        exact ⟨p, hp', rfl⟩
      exact hy.1
  have hs : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} := by
    rw [← (quasi_coherent_ideal_zero_set_affine X K).2.2.2.2
      K.subscheme K.subschemeι (IdealSheafData.ker_subschemeι K)]
    rw [IdealSheafData.range_subschemeι]
    simpa [K] using hSupp
  have h := hloc.mp hs
  have hex : ∀ U : S, ∃ n : ℕ,
      K.ideal U.1 ^ n ≤ Module.annihilator Γ(X, U.1.1) Γ(F, U.1.1) := by
    intro U
    have : IsNoetherianRing Γ(X, U.1.1) :=
      IsLocallyNoetherian.component_noetherian U.1
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h U.1 U.2)
      (Ideal.fg_of_isNoetherianRing _)
  choose n hn using hex
  let T := hfin.toFinset
  let t := T.sup fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0
  have : K.toModules.IsQuasicoherent := ideal_qc K K.toModules (Iso.refl _)
  refine ⟨t, (powerProduct_isZero_iff_affine_cover X F K.toModulesι S hS t).mpr ?_⟩
  intro U hU
  have hnt : n ⟨U, hU⟩ ≤ t := by
    have hm : U ∈ T := hfin.mem_toFinset.mpr hU
    simpa only [dite_eq_left hU] using Finset.le_sup
      (f := fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0) hm
  have hr : (LinearMap.range (K.toModulesι.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
      K.ideal U := SetLike.coe_injective (K.range_toModulesι_app U)
  rw [hr]
  exact (Ideal.pow_le_pow_right hnt).trans (hn ⟨U, hU⟩)


end AlgebraicGeometry.Scheme.Modules
