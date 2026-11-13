import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Equality of adjacent unequal-rank JPSS Laurent spans

This proposition isolates the block comparison in the final paragraph of the
proof of JPSS Theorem 2.7(i)-(ii), printed p.395. It does not prove that comparison
or assert convergence, rationality or existence of a normalized generator.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Adjacent allowed rectangular blocks have the same Laurent span of their
actual rational continuations. All data and hypotheses preceding the conclusion
are those of `UnequalRankCommonGeneratorStatement`; the additive Haar measure is
arbitrary, and the natural-number equalities transport only the large-rank types. -/
def UnequalRankAdjacentBlockSpanStatement (n r : ℕ) : Prop :=
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
  n < r →
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ ν : AdditiveHaarMeasure F,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
            zetaSpan
              (unequalRankValuesAt (j + 1) k (by omega) T.residueCardinality ψ
                (normalizedAbsoluteValue T) μ (rectangularMeasure ν (j + 1) (n + 1))
                π σ ℓ ℓ') =
            zetaSpan
              (unequalRankValuesAt j (k + 1) (by omega) T.residueCardinality ψ
                (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1))
                π σ ℓ ℓ')

end Langlands.AllField.RankinSelberg
