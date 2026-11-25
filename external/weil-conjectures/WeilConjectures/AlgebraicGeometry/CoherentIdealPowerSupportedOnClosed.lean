/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence

/-! # Concentrating an ideal-power product on a closed subset

Source: Stacks Project, Tags 01YD and 01Y9.
(blueprint: lem-pc-s3-coherent-ideal-power-supported-on-closed)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ideal-power product can be made to vanish away from a prescribed closed subset.

Source: Stacks Project, Tag 01YD, proof of Lemma 30.12.1, applying Tag 01Y9,
Lemma 30.10.2 (https://stacks.math.columbia.edu/tag/01YD).
(blueprint: lem-pc-s3-coherent-ideal-power-supported-on-closed)

Proof: Cover V = X minus C by finitely many affine opens of X. Coherence gives
quasi-coherence and finite type; on each affine the nonzero-stalk locus is the zero
locus of the annihilator of the section module. The hypothesis, restricted to an
affine contained in V, places this locus in the zero locus of K's section ideal.
Thus the section ideal lies in the radical of the annihilator. The affine section
ring is Noetherian, so the ideal is finitely generated and some power annihilates
the section module. Take the maximum of these finitely many powers; powers are
decreasing, so this exponent kills the module on each member of the cover.
The general helpers in CoherentSupportVanishingIdealNilpotence identify the
sections of the recursively constructed ideal powers with algebraic ideal powers
and prove quasi-coherence. Tensor and image quasi-coherence give quasi-coherence
of the product. Its image inclusion is injective on sections, and its affine range
is the ideal power times the section module, hence zero on the chosen cover.
Quasi-coherence identifies each affine restriction with the sheaf associated to
its zero section module. Restriction identifies its stalks with the ambient ones,
so the product has zero stalk at every point outside C. The empty cover gives
exponent zero. No restriction comparison for ideal powers, coherent product or
quotient, exact sequence, or strict support containment is needed. -/
theorem coherent_ideal_power_supported_on_closed
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (K : X.IdealSheafData) (C : TopologicalSpace.Closeds X)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      (K.support : Set X) ∪ (C : Set X)) :
    ∃ n : ℕ, (idealSheafPower K.toModulesι n).1.IsQuasicoherent ∧
      {x : X | ¬ Subsingleton
        ((idealModuleProduct (idealSheafPower K.toModulesι n).2 F).presheaf.stalk x)} ⊆
        (C : Set X) := by
  open CategoryTheory CategoryTheory.Limits Opposite in
    classical
    have : F.IsQuasicoherent :=
      ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
    have : F.IsFiniteType :=
      ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).2
    have : K.toModules.IsQuasicoherent := ideal_qc K K.toModules (Iso.refl _)
    let V : X.Opens := ⟨(C : Set X)ᶜ, C.isClosed.isOpen_compl⟩
    obtain ⟨S, hfin, hcover⟩ :=
      isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
        ⟨TopologicalSpace.NoetherianSpace.isCompact (V : Set X), V.isOpen⟩
    have hUV (U : X.affineOpens) (hU : U ∈ S) : (U.1 : Set X) ⊆ V := by
      rw [hcover]
      exact Set.subset_iUnion_of_subset U (Set.subset_iUnion_of_subset hU Set.Subset.rfl)
    have hS (x : X) (hx : x ∈ V) : ∃ U ∈ S, x ∈ U.1 := by
      change x ∈ (V : Set X) at hx
      rw [hcover] at hx
      obtain ⟨U, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hU, hx⟩ := Set.mem_iUnion.mp hx
      exact ⟨U, hU, hx⟩
    have hsupp := (finite_type_module_support_closed X F).2.2.1
    have hloc (U : X.affineOpens) (hU : U ∈ S) :
        K.ideal U ≤ (Module.annihilator Γ(X, U.1) Γ(F, U.1)).radical := by
      apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp
      intro p hp
      have hx : U.2.fromSpec p ∈
          {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) := by
        rw [hsupp U]
        exact ⟨p, hp, rfl⟩
      have hxK : U.2.fromSpec p ∈ (K.support : Set X) :=
        (hSupp hx.1).resolve_right (hUV U hU hx.2)
      have hy : U.2.fromSpec p ∈
          U.2.fromSpec '' PrimeSpectrum.zeroLocus (K.ideal U : Set Γ(X, U.1)) := by
        rw [U.2.fromSpec_image_zeroLocus, ← K.coe_support_inter U]
        exact ⟨hxK, hx.2⟩
      obtain ⟨q, hq, heq⟩ := hy
      have he : q = p := U.2.fromSpec.isOpenEmbedding.injective heq
      exact he ▸ hq
    have hex : ∀ U : S, ∃ n : ℕ,
        K.ideal U.1 ^ n ≤ Module.annihilator Γ(X, U.1.1) Γ(F, U.1.1) := by
      intro U
      have : IsNoetherianRing Γ(X, U.1.1) :=
        IsLocallyNoetherian.component_noetherian U.1
      exact Ideal.exists_pow_le_of_le_radical_of_fg (hloc U.1 U.2)
        (Ideal.fg_of_isNoetherianRing _)
    choose n hn using hex
    let T := hfin.toFinset
    let t := T.sup fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0
    have hkill (U : X.affineOpens) (hU : U ∈ S) :
        K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
      have hnt : n ⟨U, hU⟩ ≤ t := by
        have hm : U ∈ T := hfin.mem_toFinset.mpr hU
        simpa only [dite_eq_left hU] using Finset.le_sup
          (f := fun U ↦ if hU : U ∈ S then n ⟨U, hU⟩ else 0) hm
      exact (Ideal.pow_le_pow_right hnt).trans (hn ⟨U, hU⟩)
    have hpow := (powers_affine_sections K.toModulesι t).1
    have : (idealSheafPower K.toModulesι t).1.IsQuasicoherent := hpow
    let J := (idealSheafPower K.toModulesι t).1
    let i : J ⟶ SheafOfModules.unit X.ringCatSheaf := (idealSheafPower K.toModulesι t).2
    let H := idealModuleProduct i F
    have : (MonoidalCategory.tensorObj J F).IsQuasicoherent :=
      (quasiCoherent_tensor_product_affine_sections J F).1
    have hH : H.IsQuasicoherent := by
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      let f := MonoidalCategory.whiskerRight i F ≫ (MonoidalCategory.leftUnitor F).hom
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (Abelian.imageIsoImage f)
        (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1
    have : H.IsQuasicoherent := hH
    have hsec (U : X.affineOpens) (hU : U ∈ S) : Subsingleton Γ(H, U.1) := by
      have hr := multiplication_range i F U
        ((quasiCoherent_tensor_product_affine_sections J F).2 U.1 U.2).2
      have hi : (LinearMap.range (i.val.app (op U.1)).hom : Ideal Γ(X, U.1)) =
          K.ideal U ^ t := by
        rw [(powers_affine_sections K.toModulesι t).2 U]
        exact congrArg (fun I : Ideal Γ(X, U.1) ↦ I ^ t)
          (SetLike.coe_injective (K.range_toModulesι_app U))
      rw [hi] at hr
      have hbot : K.ideal U ^ t • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ≤ ⊥ := by
        apply Submodule.smul_le.mpr
        intro a ha m _
        exact Module.mem_annihilator.mp (hkill U hU ha) m
      have hz (s : Γ(H, U.1)) : (idealModuleProductι i F).app U.1 s = 0 := by
        apply hbot
        exact (Set.ext_iff.mp hr _).mp ⟨s, rfl⟩
      have : Mono (idealModuleProductι i F) := by
        dsimp [idealModuleProductι]
        infer_instance
      have hinj := (ModuleCat.mono_iff_injective _).mp
        ((SheafOfModules.evaluation _ (op U.1)).map_mono (idealModuleProductι i F))
      exact ⟨fun a b ↦ hinj ((hz a).trans (hz b).symm)⟩
    refine ⟨t, hpow, ?_⟩
    intro x hx
    by_contra hxC
    obtain ⟨U, hU, hxU⟩ := hS x hxC
    have : Subsingleton Γ(H, U.1.ι ''ᵁ ⊤) := by
      simpa only [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
        using hsec U hU
    have hz : IsZero (H.restrict U.1.ι) := affine_source_zero_of_sections H U.1.ι
    let y : U.1.toScheme := ⟨x, hxU⟩
    have hs : Subsingleton ((H.restrict U.1.ι).presheaf.stalk y) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((RingedSpace.moduleStalkFunctor U.1.toScheme.toRingedSpace y).map_isZero hz)
    have e := ((restrictStalkNatIso U.1.ι y).app H).addCommGroupIsoToAddEquiv.toEquiv
    exact hx (e.subsingleton_congr.mp hs)

end AlgebraicGeometry.Scheme.Modules
