import Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Zero-row unequal-rank convergence, rationality and a common denominator

This proposition isolates the first three analytic conclusions at zero rows
for every positive rank gap. It is a statement target, not an analytic proof.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankZeroRowAnalyticStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The diagonal restriction integrals in JPSS p.394, equation (7), converge
in a right half-plane and have rational continuations with a common denominator
over all coefficient-model functions. The ranks differ by the arbitrary positive
gap `k + 1`; all hypotheses are those of `UnequalRankAnalyticStatement F T n 0 k`.
Normalized-generator existence and unit-span membership are separate targets. -/
def UnequalRankZeroRowAnalyticStatement (n k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ ν : AdditiveHaarMeasure F,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ
          (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType (n + (0 + k + 1)) (standardCharacter ψ (n + (0 + k + 1))) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
          (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          (∀ f : (coefficientModel π ℓ).toSubmodule,
            ∀ f' : (coefficientModel σ ℓ').toSubmodule,
              ∃ a : ℝ, ∀ s : ℂ, a < s.re →
                UnequalRankConverges ψ (normalizedAbsoluteValue T) 0 k
                  μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
          (∀ f : (coefficientModel π ℓ).toSubmodule,
            ∀ f' : (coefficientModel σ ℓ').toSubmodule,
              ∃ R : RationalFunctions,
                HasRationalContinuation T.residueCardinality
                  (unequalRankModelIntegral ψ (normalizedAbsoluteValue T) 0 k
                    μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f') R) ∧
          HasCommonDenominator
            (unequalRankRationalValues 0 k T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ')

end Langlands.AllField.RankinSelberg
