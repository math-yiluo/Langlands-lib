import Langlands.Representation.RankinSelberg.QuotientAnalyticStatement
import Langlands.AllField.Representation.RankinSelberg.QuotientRootIntegrationStatement
import Langlands.AllField.Representation.RankinSelberg.RootAverageAnalyticStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Conditional convergence and rationality of the actual equal-rank quotient
integrals, with one denominator before all functionals and compatible measures. -/
def EqualRankQuotientAnalyticStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  FiniteFunctionMellinStatement.{uF} →
  QuotientIwasawaIntegrationStatement F T n →
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ψ : UnitaryAdditiveCharacter F),
    IsSmooth π → IsSmooth σ →
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ d : LaurentCoefficients, d ≠ 0 ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
        ∃ b : ℝ, ∀ s : ℂ, b < s.re →
          EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s) ∧
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
        ∃ R : RationalFunctions, HasRationalContinuation T.residueCardinality
          (equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ) R) ∧
      (∀ R ∈ equalRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ',
        ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc d * R)

end Langlands.AllField.RankinSelberg
