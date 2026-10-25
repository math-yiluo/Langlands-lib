import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Classification.Tempered
import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Sharp square-integrable convergence and holomorphy at zero rows

JPSS Section 8.3, printed pages 448–451, for unequal ranks and rectangular
block zero. Holomorphy is the derived analytic formulation explained in the
paired Markdown. This module defines a proposition; it does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The zero-row integral of two irreducible square-integrable representations
converges absolutely and is holomorphic on `Re(s) > 0`, for every supplied
compatible quotient measure and additive Haar measure. Square-integrability
is the analytic predicate modulo the center for the supplied topology. -/
def SquareIntegrableZeroRowAnalyticStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n k : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ
          (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        Representation.IsIrreducible π → T.IsSquareIntegrable π →
        Representation.IsIrreducible σ → T.IsSquareIntegrable σ →
        ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
          (ℓ' : glInverseFunctionals ψ n σ),
          ∀ (f : (coefficientModel π ℓ).toSubmodule)
            (f' : (coefficientModel σ ℓ').toSubmodule),
            (∀ s : ℂ, 0 < s.re →
              UnequalRankConverges ψ (normalizedAbsoluteValue T) 0 k
                μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
            DifferentiableOn ℂ
              (unequalRankModelIntegral ψ (normalizedAbsoluteValue T) 0 k
                μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f')
              {s : ℂ | 0 < s.re}

end Langlands.RankinSelberg
