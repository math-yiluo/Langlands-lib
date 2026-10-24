import Langlands.Representation.RankinSelberg.RootAverageAnalyticStatement
import Langlands.Representation.RankinSelberg.QuotientRootIntegrationStatement

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Conditional convergence and rationality of the actual equal-rank quotient
integrals, with one denominator before all functionals and compatible measures. -/
def EqualRankQuotientAnalyticStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  FiniteFunctionMellinStatement.{uF} →
  QuotientIwasawaIntegrationStatement F T n →
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    IsSmooth π → IsSmooth σ →
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ d : LaurentCoefficients, d ≠ 0 ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        ∃ b : ℝ, ∀ s : ℂ, b < s.re →
          EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s) ∧
      (∀ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        ∃ R : RationalFunctions, HasRationalContinuation T.residueCardinality
          (equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ) R) ∧
      (∀ R ∈ equalRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ',
        ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc d * R)

end Langlands.RankinSelberg
