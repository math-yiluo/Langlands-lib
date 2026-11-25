/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingChart
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedMatchingChartPowerLift
import WeilConjectures.RingTheory.FormalGlueingH0Localization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # The localized formal-gluing comparison on a principal chart

## References

* Stacks Project, Tags 0BLH and 05ER (localized affine chart comparison)
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
  exact Algebra.algebra_ext _ _ (fun b ↦ congrArg (fun k : B →+* Γ(X, ⊤) ↦ k b) he.symm)

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

set_option backward.isDefEq.respectTransparency false in
private theorem matching_chart_kernel
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A) (hf :
      (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∀ z : D.matchingRing, ψ (ρ z) = 0 →
      ∃ n : ℕ, D.baseMap.hom f ^ n * z = 0 := by
  classical
  let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
  let ρ := ((ΓSpecIso D.matchingRing).inv ≫
    (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
  let ψ := (D.puncturedMap ∣_ W).appTop.hom
  change ∀ z : D.matchingRing, ψ (ρ z) = 0 →
    ∃ n : ℕ, D.baseMap.hom f ^ n * z = 0
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have hfm : f ∈ IsLocalRing.maximalIdeal A := by
    by_contra h
    have hx : IsLocalRing.closedPoint A ∈ PrimeSpectrum.basicOpen f := by
      exact h
    exact ((hU _).mp (hf hx)) rfl
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  change Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A at hg
  let g' : Fin (r + 1) → A := Fin.cons f g
  have hg' : Ideal.span (Set.range g') = IsLocalRing.maximalIdeal A := by
    rw [show Set.range g' = insert f (Set.range g) from Fin.range_cons f g]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro a ha
      rcases ha with rfl | ha
      · exact hfm
      · exact hg ▸ Ideal.subset_span ha
    · rw [← hg]
      exact Ideal.span_mono (Set.subset_insert f (Set.range g))
  let : Algebra A D.matchingRing := D.baseMap.hom.toAlgebra
  let : Algebra A Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
    ((ψ.comp ρ).comp D.baseMap.hom).toAlgebra
  have hchart :=
    D.exists_formalGlueingData_matching_chart hU (r + 1) g' hg' 0
  dsimp only at hchart
  obtain ⟨X, b, c, hc⟩ := hchart
  have hflat : (algebraMap A C).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨π, hπ, _, hbij⟩ := FormalGlueing.exists_unique_bijective_h0_localization
    (algebraMap A C) hflat g' X 0
  intro z hz
  have hcoord : (b.symm z).val.2 0 = 0 := by
    apply c.injective
    exact (hc (b.symm z)).symm.trans
      ((congrArg (fun x ↦ ψ (ρ x)) (b.apply_symm_apply z)).trans
        (hz.trans c.map_zero.symm))
  have hzero : LocalizedModule.mk (S := Submonoid.powers (g' 0)) (b.symm z) 1 =
      LocalizedModule.mk (0 : FormalGlueing.h0 (algebraMap A C) g' X) 1 := by
    apply hbij.injective
    rw [hπ, hπ, hcoord]
    rfl
  obtain ⟨a, ha⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers (g' 0))
    (f := LocalizedModule.mkLinearMap _ (FormalGlueing.h0 (algebraMap A C) g' X)) hzero
  obtain ⟨n, hn⟩ := a.property
  refine ⟨n, ?_⟩
  change (a : A) • b.symm z = (a : A) •
    (0 : FormalGlueing.h0 (algebraMap A C) g' X) at ha
  have hb := congrArg b ha
  simp only [b.map_smul, smul_zero, b.map_zero, b.apply_symm_apply] at hb
  change D.baseMap.hom (a : A) * z = 0 at hb
  rw [← hn, map_pow] at hb
  exact hb

/-- The localized formal-gluing comparison is a ring equivalence on the
principal chart, compatible with the matching numerator. -/
theorem puncturedMatching_chart_restriction_ringEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A) (hf :
      (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∃ e : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) ≃+*
      Γ(W.toScheme, ⊤),
      ∀ b : D.matchingRing, e (ψ (ρ b)) = ρ b := by
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
  have hker := matching_chart_kernel hU D f hf
  have : IsLocalization.Away r Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
    { map_units := fun m ↦ (IsLocalization.map_units Γ(W.toScheme, ⊤) m).map ψ
      surj := fun t ↦ by
        obtain ⟨n, b, hb⟩ := hlift t
        refine ⟨(b, ⟨r ^ n, ⟨n, rfl⟩⟩), ?_⟩
        change t * ψ (ρ (r ^ n)) = ψ (ρ b)
        simpa only [map_pow, mul_comm] using hb.symm
      exists_of_eq := fun {b c} h ↦ by
        change ψ (ρ b) = ψ (ρ c) at h
        have hz : ψ (ρ (b - c)) = 0 := by
          simpa only [map_sub, sub_eq_zero] using h
        obtain ⟨n, hn⟩ := hker (b - c) hz
        refine ⟨⟨r ^ n, ⟨n, rfl⟩⟩, ?_⟩
        exact sub_eq_zero.mp (by simpa only [mul_sub] using hn) }
  have hbij : Function.Bijective ψ :=
    IsLocalization.bijective (Submonoid.powers r) ψ rfl
  refine ⟨(RingEquiv.ofBijective ψ hbij).symm, ?_⟩
  intro b
  exact (RingEquiv.ofBijective ψ hbij).symm_apply_apply (ρ b)

end AlgebraicGeometry.Scheme.CompletionGluingData
