/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.RingTheory.FormalGlueingH0Localization
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedMatchingChartRestrictionInverse

/-! # Vanishing of a localized matching numerator

## References

* Stacks Project, Tag 0BLH, proof (construction of the chart algebras), and Tag 05ER, proof
  (localized first-projection comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- A matching-ring numerator whose punctured chart section vanishes has zero
section on the corresponding principal open of the affine candidate. -/
theorem puncturedMatching_chart_section_injective
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
    ∀ b : D.matchingRing, ψ (ρ b) = 0 → ρ b = 0 := by
  dsimp only
  obtain ⟨g, hg⟩ := puncturedMatching_chart_restriction_leftInverse hU D f hf
  intro b hb
  have h := hg b
  rw [hb, map_zero] at h
  exact h.symm

end AlgebraicGeometry.Scheme.CompletionGluingData
