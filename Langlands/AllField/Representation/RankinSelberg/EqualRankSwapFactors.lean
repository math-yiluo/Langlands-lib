import Langlands.Representation.RankinSelberg.EqualRankSwapFactors
import Langlands.AllField.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-! Universal factor-certificate transport at the original character. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply unipotentCharacterChangeModulus
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration

universe uF uV uW

section Relations



end Relations

section Padic


/-- Fixed-character epsilon exchange for arbitrary equal-rank representations
of Whittaker type, at the same supplied additive Haar measure. -/
theorem isPadicPairEpsilonFactor_swap_equalRank
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (e : ℂˣ × ℤ) :
    IsPadicPairEpsilonFactor F ψ ν π σ e ↔
      IsPadicPairEpsilonFactor F ψ ν σ π e := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  change IsPairEpsilonFactor _ _ _ _ _ _ _ ↔ IsPairEpsilonFactor _ _ _ _ _ _ _
  rw [isPairEpsilonFactor_self, isPairEpsilonFactor_self]
  have hLaw : ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)]
      (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (-1) μ := by
    intro hinv μ hμ
    exact characterChangeCompatibleMeasure F (⟨⟩ : LocalFieldData F) n (-1) μ hμ
  exact ⟨IsEqualRankEpsilonFactor.negOne_swap _ ψ _ ν π σ hπ hLaw,
    IsEqualRankEpsilonFactor.negOne_swap _ ψ _ ν σ π hσ hLaw⟩

/-- Fixed-character gamma exchange obtained from the actual gamma equations,
without any analytic or factor-existence premise. -/
theorem isPadicPairGammaFactor_swap_equalRank
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (G : RationalFunctions) :
    IsPadicPairGammaFactor F ψ ν π σ G ↔
      IsPadicPairGammaFactor F ψ ν σ π G := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  change IsPairGammaFactor _ _ _ _ _ _ _ ↔ IsPairGammaFactor _ _ _ _ _ _ _
  rw [isPairGammaFactor_self, isPairGammaFactor_self]
  have hLaw : ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)]
      (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (-1) μ := by
    intro hinv μ hμ
    exact characterChangeCompatibleMeasure F (⟨⟩ : LocalFieldData F) n (-1) μ hμ
  exact ⟨IsEqualRankGammaFactor.negOne_swap _ ψ _ ν π σ hπ hLaw,
    IsEqualRankGammaFactor.negOne_swap _ ψ _ ν σ π hσ hLaw⟩

end Padic

end Langlands.AllField.RankinSelberg
