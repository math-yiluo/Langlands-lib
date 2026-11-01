import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaIntegrals
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaScalar

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV uW

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  (q : ℕ) (hq : 1 < q)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ n π) (L' : glInverseFunctionals ψ n σ)

include h₁ h₂ hprod in
/-- Transport the whole equal-rank fixed-functional gamma certificate, including
the nonzero rational witness and every Fourier test. -/
theorem equal_equation {G : RationalFunctions}
    (h : EqualRankGammaEquation q ψ abv μ ν π σ L L' G) :
    EqualRankGammaEquation q ψ abv μ ν
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (functional χ₁ π L) (functional χ₂ σ L')
      (rationalRescale (spectralShiftUnit q hq u) G) := by
  obtain ⟨ζ, hζ, ⟨R, ⟨f, f', Φ, hR⟩, hR0⟩, hall⟩ := h
  refine ⟨ζ, minusOne χ₂ h₂ σ L' hζ, ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨rationalRescale (spectralShiftUnit q hq u) R,
      ⟨modelMap _ _ v, modelMap _ _ w, Φ, ?_⟩, ?_⟩
    · rw [equal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w Φ]
      exact hR.shift hq u
    · simpa only [map_zero] using
        (rationalRescale (spectralShiftUnit q hq u)).injective.ne hR0
  · intro f f' Φ
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    obtain ⟨Φhat, R, Rd, hΦ, hR, hRd, heq⟩ :=
      hall (modelMap _ _ v) (modelMap _ _ w) Φ
    refine ⟨Φhat, rationalRescale (spectralShiftUnit q hq u) R,
      rationalRescale (spectralShiftUnit q hq (-u)) Rd, hΦ, ?_, ?_, heq.shift hq u⟩
    · rw [equal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w Φ]
      exact hR.shift hq u
    · rw [equal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w Φhat]
      simpa only [sub_eq_add_neg] using hRd.shift hq (-u)

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  {r n : ℕ} (hnr : n < r) (q : ℕ) (hq : 1 < q)
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ r π) (L' : glInverseFunctionals ψ n σ)

include h₁ h₂ hprod in
/-- Transport every rectangular decomposition of the whole unequal-rank
fixed-functional gamma certificate, retaining its nonzero witnesses. -/
theorem unequal_equation {G : RationalFunctions}
    (h : UnequalRankGammaEquation hnr q ψ abv μ ν π σ L L' G) :
    UnequalRankGammaEquation hnr q ψ abv μ ν
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (functional χ₁ π L) (functional χ₂ σ L')
      (rationalRescale (spectralShiftUnit q hq u) G) := by
  obtain ⟨ζ, hζ, hall⟩ := h
  refine ⟨ζ, minusOne χ₂ h₂ σ L' hζ, ?_⟩
  intro j k hr
  obtain ⟨⟨R, hRmem, hR0⟩, hFE⟩ := hall j k hr
  refine ⟨?_, ?_⟩
  · rw [unequalRankValuesAt_eq] at hRmem
    obtain ⟨f, f', hR⟩ := hRmem
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨rationalRescale (spectralShiftUnit q hq u) R, ?_, ?_⟩
    · rw [unequalRankValuesAt_eq]
      refine ⟨modelMap _ _ v, modelMap _ _ w, ?_⟩
      rw [unequal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w j k hr]
      exact hR.shift hq u
    · simpa only [map_zero] using
        (rationalRescale (spectralShiftUnit q hq u)).injective.ne hR0
  · intro f f'
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ w)
    refine ⟨rationalRescale (spectralShiftUnit q hq u) R,
      rationalRescale (spectralShiftUnit q hq (-u)) Rd, ?_, ?_, heq.shift hq u⟩
    · rw [unequal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w j k hr]
      exact hR.shift hq u
    · rw [unequal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w hnr j k hr ν]
      simpa only [sub_eq_add_neg] using hRd.shift hq (-u)

end UnequalRank

end Langlands.RankinSelberg.UnramifiedGammaTwist
