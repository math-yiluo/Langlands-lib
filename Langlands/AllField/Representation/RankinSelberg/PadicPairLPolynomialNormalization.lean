import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
/-! Constant-term normalization of p-adic pair L-polynomial certificates. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.LocalFieldData

universe uF uV uW


section Normalization

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F}
  {ν : letI := borel F
    AdditiveHaarMeasure F}
  {r t : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
  {P : ℂ[X]}

/-- The p-adic relation inherits the normalization of its integral generator. -/
theorem IsPadicPairLPolynomial.coeff_zero (h : IsPadicPairLPolynomial F ψ ν π σ P) :
    P.coeff 0 = 1 := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (t + 1) F)
  let : BorelSpace (GeneralLinear.upperUnipotent (t + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F)
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).coeff_zero

/-- Reading the larger rank first preserves the constant-term normalization. -/
theorem IsPadicSymmetricLPolynomial.coeff_zero
    (h : IsPadicSymmetricLPolynomial F ψ ν π σ P) : P.coeff 0 = 1 := by
  unfold IsPadicSymmetricLPolynomial at h
  split_ifs at h
  · exact h.coeff_zero
  · exact h.coeff_zero

end Normalization

end Langlands.AllField.RankinSelberg
