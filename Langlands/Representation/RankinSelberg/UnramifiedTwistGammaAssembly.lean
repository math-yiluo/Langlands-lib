import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.Whittaker.Twist

/-! # Complete gamma certificates from fixed-functional twist transport -/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory QuotientIntegration

universe uF uV uW

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F) (χ₁ χ₂ : Fˣ →* ℂˣ)
  (T : RationalFunctions → RationalFunctions)

/-- Fixed-functional transport implies transport of the full equal-rank
certificate. The same compatible measures are retained, and arbitrary
functionals of the twisted representations are untwisted without changing their
underlying linear maps. -/
theorem equal_factor_of_equation
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions)
    (H : ∀ (μ : Measure (LeftUnipotentQuotient n F))
      (L : glFunctionals ψ n π) (L' : glInverseFunctionals ψ n σ),
      EqualRankGammaEquation q ψ abv μ ν π σ L L' G →
        EqualRankGammaEquation q ψ abv μ ν
          (Langlands.twist (χ₁.comp determinant) π)
          (Langlands.twist (χ₂.comp determinant) σ)
          (twistFunctional _ _ (χ₁.comp determinant)
            (determinantCharacter_unipotent χ₁) π L)
          (twistFunctional _ _ (χ₂.comp determinant)
            (determinantCharacter_unipotent χ₂) σ L') (T G))
    (h : IsEqualRankGammaFactor q ψ abv ν π σ G) :
    IsEqualRankGammaFactor q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ) (T G) := by
  obtain ⟨hμ, ⟨L, hL⟩, ⟨L', hL'⟩, hall⟩ := h
  refine ⟨hμ,
    ⟨twistFunctional _ _ (χ₁.comp determinant)
      (determinantCharacter_unipotent χ₁) π L, hL⟩,
    ⟨twistFunctional _ _ (χ₂.comp determinant)
      (determinantCharacter_unipotent χ₂) σ L', hL'⟩, ?_⟩
  intro hinv μ hμc K K' hK hK'
  let L₀ := untwistFunctional _ _ (χ₁.comp determinant)
    (determinantCharacter_unipotent χ₁) π K
  let L₀' := untwistFunctional _ _ (χ₂.comp determinant)
    (determinantCharacter_unipotent χ₂) σ K'
  exact H μ L₀ L₀' (@hall hinv μ hμc L₀ L₀' hK hK')

/-- Fixed-functional transport implies transport of the full unequal-rank
certificate, including every rectangular decomposition carried by its
fixed-functional equation. -/
theorem unequal_factor_of_equation (hnr : n < r)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions)
    (H : ∀ (μ : Measure (LeftUnipotentQuotient n F))
      (L : glFunctionals ψ r π) (L' : glInverseFunctionals ψ n σ),
      UnequalRankGammaEquation hnr q ψ abv μ ν π σ L L' G →
        UnequalRankGammaEquation hnr q ψ abv μ ν
          (Langlands.twist (χ₁.comp determinant) π)
          (Langlands.twist (χ₂.comp determinant) σ)
          (twistFunctional _ _ (χ₁.comp determinant)
            (determinantCharacter_unipotent χ₁) π L)
          (twistFunctional _ _ (χ₂.comp determinant)
            (determinantCharacter_unipotent χ₂) σ L') (T G))
    (h : IsUnequalRankGammaFactor hnr q ψ abv ν π σ G) :
    IsUnequalRankGammaFactor hnr q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ) (T G) := by
  obtain ⟨hμ, ⟨L, hL⟩, ⟨L', hL'⟩, hall⟩ := h
  refine ⟨hμ,
    ⟨twistFunctional _ _ (χ₁.comp determinant)
      (determinantCharacter_unipotent χ₁) π L, hL⟩,
    ⟨twistFunctional _ _ (χ₂.comp determinant)
      (determinantCharacter_unipotent χ₂) σ L', hL'⟩, ?_⟩
  intro hinv μ hμc K K' hK hK'
  let L₀ := untwistFunctional _ _ (χ₁.comp determinant)
    (determinantCharacter_unipotent χ₁) π K
  let L₀' := untwistFunctional _ _ (χ₂.comp determinant)
    (determinantCharacter_unipotent χ₂) σ K'
  exact H μ L₀ L₀' (@hall hinv μ hμc L₀ L₀' hK hK')

end Relations

end Langlands.RankinSelberg.UnramifiedGammaTwist
