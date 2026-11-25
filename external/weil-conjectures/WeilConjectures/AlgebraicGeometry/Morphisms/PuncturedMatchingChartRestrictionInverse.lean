/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedMatchingChartRestrictionRingEquiv

/-! # A left inverse to the principal-chart comparison

## References

* Stacks Project, Tags 0BLH and 05ER
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The principal-chart comparison on the image of the matching ring admits a
ring-theoretic left inverse. -/
theorem puncturedMatching_chart_restriction_leftInverse
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
    ∃ g : Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) →+* Γ(W.toScheme, ⊤),
      ∀ b : D.matchingRing, g (ψ (ρ b)) = ρ b := by
  dsimp only
  obtain ⟨e, he⟩ := puncturedMatching_chart_restriction_ringEquiv hU D f hf
  exact ⟨e.toRingHom, he⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
