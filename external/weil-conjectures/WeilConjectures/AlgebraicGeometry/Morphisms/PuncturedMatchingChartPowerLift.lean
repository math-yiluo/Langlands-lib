/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingChart
import WeilConjectures.RingTheory.FormalGlueingH0ChartPowerLift
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Data.Fin.Tuple.Basic

/-! # Denominator lifting for punctured matching sections

## References

* Stacks Project, Tags 0BLH and 05ER, localized chart comparison
* Stacks Project, Tag 05ER, the localized chart comparison in its proof, using 05EP and 05EQ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

set_option backward.isDefEq.respectTransparency false in
/-- Every chart section lifts to a matching section after clearing a power of `f`. -/
theorem puncturedMatching_chart_power_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    ∀ t : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤),
      ∃ (n : ℕ) (b : D.matchingRing),
        ψ (ρ b) = ψ (ρ (D.baseMap.hom f)) ^ n * t := by
  classical
  let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
  let ρ := ((ΓSpecIso D.matchingRing).inv ≫
    (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
  let ψ := (D.puncturedMap ∣_ W).appTop.hom
  change ∀ t : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤),
    ∃ (n : ℕ) (b : D.matchingRing),
      ψ (ρ b) = ψ (ρ (D.baseMap.hom f)) ^ n * t
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
  intro t
  obtain ⟨n, h, hh⟩ := FormalGlueing.h0_chart_power_lift
    (algebraMap A C) hflat g' X 0 (c.symm t)
  refine ⟨n, b h, ?_⟩
  have hc' : ψ (ρ (b h)) = c (h.val.2 0) := by
    exact hc h
  refine hc'.trans ((congrArg c hh).trans ((c.map_smul _ _).trans ?_))
  refine (congrArg (fun x : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) ↦ g' 0 ^ n • x)
    (c.apply_symm_apply t)).trans ?_
  change ((ψ.comp ρ).comp D.baseMap.hom) (g' 0 ^ n) * t = _
  simp only [g', Fin.cons_zero, map_pow, RingHom.comp_apply]

end AlgebraicGeometry.Scheme.CompletionGluingData
