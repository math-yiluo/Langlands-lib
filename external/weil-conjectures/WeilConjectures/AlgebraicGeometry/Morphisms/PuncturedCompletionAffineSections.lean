/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedMatchingChartPowerLift
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedMatchingChartKernelTorsion

/-! # The localized ring equivalence behind the punctured section comparison

## References

* Stacks Project, Tags 0BLH, 05ER and 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

set_option backward.isDefEq.respectTransparency false in
private theorem principalOpen_sections_localization
    {B : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec B)
    [IsOpenImmersion j] (r : B)
    (hj : j ''ᵁ (⊤ : X.Opens) = PrimeSpectrum.basicOpen r) :
    let := ((ΓSpecIso B).inv ≫ j.appTop).hom.toAlgebra
    IsLocalization.Away r Γ(X, ⊤) := by
  let e : Γ(Spec B, PrimeSpectrum.basicOpen r) ≅ Γ(X, ⊤) :=
    (Spec B).presheaf.mapIso (eqToIso hj).op ≪≫ j.appIso ⊤
  have he : e.hom.hom.comp (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r)) =
      ((ΓSpecIso B).inv ≫ j.appTop).hom := by
    simp only [IsAffineOpen.algebraMap_Spec_obj, ← CommRingCat.hom_comp]
    congr 1
    apply (cancel_mono (j.appIso ⊤).inv).mp
    simp only [e, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show j.appTop = j.appLE ⊤ ⊤ le_rfl by simp [Hom.appLE],
      Hom.appLE_appIso_inv]
    simp [← Functor.map_comp]
  have hloc := (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers r) e.commRingCatIsoToRingEquiv).mp inferInstance
  convert hloc using 1
  exact Algebra.algebra_ext _ _ (fun b => congrArg (fun k : B →+* Γ(X, ⊤) => k b) he.symm)

private theorem principalOpen_image
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι) ''ᵁ (⊤ : W.toScheme.Opens) =
      PrimeSpectrum.basicOpen (D.baseMap.hom f) := by
  dsimp only
  rw [Hom.comp_image, Opens.ι_image_top, image_morphismRestrict_preimage]
  rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
    inf_eq_right.mpr hf]
  exact SpecMap_preimage_basicOpen D.baseMap f

/-- For `D(f) ≤ U`, the map on global sections induced by `D.puncturedMap` over the chart
above `D(f)` is the underlying map of a ring isomorphism. -/
theorem exists_puncturedMap_basicOpen_appTop_ringEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    ∃ e : Γ(((D.modelMap ∣_ U) ⁻¹ᵁ
        (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)).toScheme, ⊤) ≃+*
        Γ((D.puncturedMap ⁻¹ᵁ ((D.modelMap ∣_ U) ⁻¹ᵁ
          (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).toScheme, ⊤),
      (e : _ → _) =
        (D.puncturedMap ∣_ ((D.modelMap ∣_ U) ⁻¹ᵁ
          (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).appTop.hom := by
  classical
  let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
  let j := W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι
  let ρ := ((ΓSpecIso D.matchingRing).inv ≫ j.appTop).hom
  let ψ := (D.puncturedMap ∣_ W).appTop.hom
  let r := D.baseMap.hom f
  let := ρ.toAlgebra
  have : IsLocalization.Away r Γ(W.toScheme, ⊤) :=
    principalOpen_sections_localization j r (principalOpen_image D f hf)
  let := (ψ.comp ρ).toAlgebra
  have hlift := D.puncturedMatching_chart_power_lift hU f hf
  have hker := D.puncturedMatching_chart_kernel_torsion hU f hf
  have : IsLocalization.Away r Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
    { map_units := fun m => (IsLocalization.map_units Γ(W.toScheme, ⊤) m).map ψ
      surj := fun t => by
        obtain ⟨n, b, hb⟩ := hlift t
        refine ⟨(b, ⟨r ^ n, ⟨n, rfl⟩⟩), ?_⟩
        change t * ψ (ρ (r ^ n)) = ψ (ρ b)
        simpa only [map_pow, mul_comm] using hb.symm
      exists_of_eq := fun {b c} h => by
        change ψ (ρ b) = ψ (ρ c) at h
        have hz : ψ (ρ (b - c)) = 0 := by
          simpa only [map_sub, sub_eq_zero] using h
        obtain ⟨n, hn⟩ := hker (b - c) hz
        refine ⟨⟨r ^ n, ⟨n, rfl⟩⟩, ?_⟩
        exact sub_eq_zero.mp (by simpa only [mul_sub] using hn) }
  have hbij : Function.Bijective ψ :=
    IsLocalization.bijective (Submonoid.powers r) ψ rfl
  exact ⟨RingEquiv.ofBijective ψ hbij, rfl⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
