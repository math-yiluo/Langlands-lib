/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine

/-! # Splitting a coherent module with reducible closed support

Source: Stacks Project, Tags 01YD and 01YF, the reducible-support paragraph.
(blueprint: lem-pc-s3-coherent-reducible-support-exact-sequence)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The reducible-support case gives a short exact sequence with two smaller supports.

Source: Stacks Project, Tag 01YD, Lemma 30.12.1, and Tag 01YF, Lemma 30.12.3,
reducible-support paragraph (https://stacks.math.columbia.edu/tag/01YD).
(blueprint: lem-pc-s3-coherent-reducible-support-exact-sequence)

Proof: A reducible closed set T is the union of two proper closed subsets T₁ and T₂:
use the closed-union characterization of preirreducibility and intersect both closed
sets with T. Tag 01YD gives a coherent submodule H of F with support in T₂ and a
coherent quotient supported in T₁. Concretely, let J be the ideal of the reduced
induced structure on T₁, and take H = J^n F. On X minus T₂, a power of J kills F
by Tag 01Y9; hence H is supported in T₂. Outside T₁ the ideal J is the unit ideal,
so F/H has zero stalk there. Coherence follows from Noetherian coherence stability
for ideal products and cokernels. The inclusion H to F is a monomorphism, and its
canonical cokernel sequence is short exact. Support containment followed by strict
inclusion T₁,T₂ into T gives both strict-support conclusions. Empty or singleton
supports cannot satisfy hred; either of H or its quotient may be zero, which causes
no exception since T is nonempty. This theorem constructs no filtration and uses
no support-induction hypothesis. -/
theorem exists_coherent_submodule_of_reducible_support
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hred : ¬ IsPreirreducible (T : Set X)) :
    ∃ (H : X.Modules) (f : H ⟶ F),
      RingedSpace.IsCoherent X.toRingedSpace H ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel f) ∧
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact ∧
      {x : X | ¬ Subsingleton (H.presheaf.stalk x)} ⊂ (T : Set X) ∧
      {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊂ (T : Set X) := by
  classical
  open MonoidalCategory in
  let product_quasiCoherent : ∀ {X : Scheme.{u}} {J : X.Modules}
      (j : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
      [J.IsQuasicoherent] [F.IsQuasicoherent],
      (idealModuleProduct j F).IsQuasicoherent := by
    intro X J j F _ _
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    have : (J ⊗ F).IsQuasicoherent :=
      (quasiCoherent_tensor_product_affine_sections J F).1
    let f := j ▷ F ≫ (λ_ F).hom
    have h := (quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.1
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage f) h
  let ideal_proper_locus : ∀ (X : Scheme.{u}) (K : X.IdealSheafData),
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} =
        (K.support : Set X) := by
    intro X K
    rw [← (quasi_coherent_ideal_zero_set_affine X K).2.2.2.2
      K.subscheme K.subschemeι (IdealSheafData.ker_subschemeι K)]
    exact IdealSheafData.range_subschemeι K
  let power_quotient_stalk_zero : ∀ {X : Scheme.{u}}
      (K : X.IdealSheafData) (F : X.Modules) (n : ℕ) (x : X),
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom →
      Subsingleton ((cokernel
        (idealModuleProductι (idealSheafPower K.toModulesι n).2 F)).presheaf.stalk x) := by
    intro X K F n x hx
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨e, he, hinj, hpinj, hr, hq, hp⟩ := ideal_module_product_stalk K.toModulesι F x
    have htop : (LinearMap.range (S.map K.toModulesι ≫ e.hom).hom :
        Ideal (X.presheaf.stalk x)) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      exact e.toLinearEquiv.surjective.comp hx
    cases n with
    | zero =>
      obtain ⟨e', he', hi', hpi', hr', ⟨q, hq'⟩, hp'⟩ :=
        ideal_module_product_stalk (𝟙 (SheafOfModules.unit X.ringCatSheaf)) F x
      have ht : (LinearMap.range (S.map (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
          e'.hom).hom : Ideal (X.presheaf.stalk x)) = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        rw [S.map_id, Category.id_comp]
        exact e'.toLinearEquiv.surjective
      rw [ht, Submodule.top_smul] at q
      exact q.symm.injective.subsingleton
    | succ n =>
      obtain ⟨hrn, hrp, q, hq⟩ := hp (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      rw [htop, Ideal.top_pow, Submodule.top_smul] at q
      exact q.symm.injective.subsingleton
  simp only [isPreirreducible_iff_isClosed_union_isClosed,
    not_forall, not_or] at hred
  obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hred
  let T₁ : TopologicalSpace.Closeds X := T ⊓ ⟨z₁, hz₁⟩
  let T₂ : TopologicalSpace.Closeds X := T ⊓ ⟨z₂, hz₂⟩
  have ht₁ : T₁ < T := inf_lt_left.mpr hn₁
  have ht₂ : T₂ < T := inf_lt_left.mpr hn₂
  have hcover' : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
      (T₁ : Set X) ∪ (T₂ : Set X) := by
    rw [hSupp]
    change (T : Set X) = ((T : Set X) ∩ z₁) ∪ ((T : Set X) ∩ z₂)
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hcover]
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  let K : X.IdealSheafData := IdealSheafData.vanishingIdeal T₁
  have hK : (K.support : Set X) = (T₁ : Set X) := by simp [K]
  have hsupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      (K.support : Set X) ∪ (T₂ : Set X) := by
    rw [hK, hcover']
  obtain ⟨n, hpow, hsub⟩ :=
    coherent_ideal_power_supported_on_closed X F hF K T₂ hsupp
  have : (idealSheafPower K.toModulesι n).1.IsQuasicoherent := hpow
  let H := idealModuleProduct (idealSheafPower K.toModulesι n).2 F
  let f : H ⟶ F := idealModuleProductι (idealSheafPower K.toModulesι n).2 F
  have hf : Mono f := by
    dsimp [f, idealModuleProductι]
    infer_instance
  have : H.IsQuasicoherent := product_quasiCoherent _ F
  obtain ⟨hH, hQ⟩ :=
    (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F H f hF hf inferInstance
  refine ⟨H, f, hH, hQ, ⟨ShortComplex.cokernelSequence_exact f⟩,
    Set.ssubset_of_subset_of_ssubset hsub ht₂, ?_⟩
  apply Set.ssubset_of_subset_of_ssubset _ ht₁
  intro x hx
  by_contra hxT₁
  have hsurj : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom := by
    by_contra hn
    have hm : x ∈ (K.support : Set X) := by
      rw [← ideal_proper_locus]
      exact hn
    exact hxT₁ (hK ▸ hm)
  exact hx (power_quotient_stalk_zero K F n x hsurj)

end AlgebraicGeometry.Scheme.Modules
