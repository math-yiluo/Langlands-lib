/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import WeilConjectures.AlgebraicGeometry.Proj.ProjTwistPullbackFractionPresentation
import WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-! The injective half of the complete standard-chart scalar-extension comparison.

## References

* Stacks Project, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The prescribed scalar-extension twist map is injective on a complete standard chart. -/
theorem scalarExtension_twistMap_chart_injective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    Function.Injective (η.app (basicOpen ℬ (ψ f))) := by
  classical
  let U := basicOpen 𝒜 f
  let V := basicOpen ℬ (ψ f)
  have hVU : V ≤ map ψ hψ ⁻¹ᵁ U :=
    le_of_eq (map_preimage_basicOpen ψ hψ f).symm
  obtain ⟨c, hcs, hc⟩ :=
    exists_twistPullback_fraction_presentation 𝒜 ℬ β ψ hβψ hgraded hψ j n f hf hn
  obtain ⟨L, hLi, hL⟩ :=
    exists_twistChartFraction_tensor_embedding 𝒜 ℬ β ψ hβψ j n f hf hn
  let evA (y : U) : Localization.Away f →+*
      Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal :=
    IsLocalization.map (M := Submonoid.powers f)
      (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id A)
      (Submonoid.powers_le.mpr y.2)
  let evB (x : V) : Localization.Away (ψ f) →+*
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal :=
    IsLocalization.map (M := Submonoid.powers (ψ f))
      (T := x.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id B)
      (Submonoid.powers_le.mpr x.2)
  have hEA (y : U) (a : A) :
      evA y (algebraMap A (Localization.Away f) a) =
        algebraMap A (Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) a :=
    IsLocalization.map_eq _ _
  have hcomp (x : V) :
      (evB x).comp (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (ψ f)) ψ.toRingHom f) =
      (Localization.localRingHom _ _ ψ.toRingHom rfl).comp
        (evA ⟨map ψ hψ x.1, hVU x.2⟩) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    have hB : evB x
        (IsLocalization.Away.map (Localization.Away f) (Localization.Away (ψ f))
          ψ.toRingHom f (algebraMap A (Localization.Away f) a)) =
        algebraMap B (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) (ψ a) := by
      simp only [IsLocalization.Away.map, evB, IsLocalization.map_eq, RingHom.id_apply]
      rfl
    exact hB.trans
      ((Localization.localRingHom_to_map _ _ ψ.toRingHom rfl a).symm.trans
        (congrArg (Localization.localRingHom _ _ ψ.toRingHom rfl)
          (hEA ⟨map ψ hψ x.1, hVU x.2⟩ a)).symm)
  have hvalue (w : TensorProduct R S (twistChartFractionSubmodule 𝒜 n f j))
      (x : V) :
      evB x (L w) = ((η.app V (c w)).1 x).val := by
    induction w using TensorProduct.inductionOn with
    | tmul s z =>
      obtain ⟨t, ht, hct⟩ := hc z
      rw [hL, hct, Hom.app_smul, Hom.app_presheaf_map]
      change evB x (s • _) =
        ((awayToSection ℬ (ψ f)
          (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) s)).1 x).val *
          ((η.app (map ψ hψ ⁻¹ᵁ U)
            (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U t)).1
              ⟨x.1, hVU x.2⟩).val
      rw [hη U t ⟨x.1, hVU x.2⟩]
      have he := congrArg (fun q : Localization.Away f →+*
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal ↦
          q (z : Localization.Away f)) (hcomp x)
      change evB x (IsLocalization.Away.map _ _ ψ.toRingHom f
        (z : Localization.Away f)) =
          Localization.localRingHom _ _ ψ.toRingHom rfl
            (evA ⟨map ψ hψ x.1, hVU x.2⟩ (z : Localization.Away f)) at he
      rw [← ht ⟨map ψ hψ x.1, hVU x.2⟩]
      rw [Algebra.smul_def, map_mul, he]
      congr 1
      have hv := ProjectiveSpectrum.Proj.awayToSection_apply ℬ (ψ f)
        (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) s)
        (show ProjectiveSpectrum.basicOpen ℬ (ψ f) from x)
      change evB x (algebraMap S (Localization.Away (ψ f)) s) = _
      apply Eq.trans ?_ hv.symm
      change _ = evB x
        ((algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) s).val)
      rw [HomogeneousLocalization.val_algebraMap]
      change evB x (algebraMap S (Localization.Away (ψ f)) s) =
        evB x (Localization.mk (algebraMap S B s) 1)
      congr 1
    | add w w' hw hw' =>
      rw [map_add, map_add, map_add, map_add]
      change evB x (L w) + evB x (L w') =
        ((η.app V (c w)).1 x).val + ((η.app V (c w')).1 x).val
      rw [hw, hw']
  intro s t hst
  obtain ⟨w, rfl⟩ := hcs s
  obtain ⟨w', rfl⟩ := hcs t
  apply congrArg c
  apply hLi
  apply basicOpen_localization_detection ℬ (ψ f) n hn (ψ.map_mem hf)
  intro x
  exact (hvalue w x).trans
    ((congrArg (fun q : Γ(twist ℬ j, V) ↦ (q.1 x).val) hst).trans
      (hvalue w' x).symm)

end AlgebraicGeometry.Proj
