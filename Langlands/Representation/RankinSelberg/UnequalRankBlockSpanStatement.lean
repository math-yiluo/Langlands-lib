import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Equality of adjacent unequal-rank JPSS Laurent spans

This proposition isolates the block comparison in the final paragraph of the
proof of JPSS Theorem 2.7(i)-(ii), printed p.395. It does not prove that comparison
or assert convergence, rationality or existence of a normalized generator.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Adjacent allowed rectangular blocks have the same Laurent span of their
actual rational continuations. All data and hypotheses preceding the conclusion
are those of `UnequalRankCommonGeneratorStatement`; the additive Haar measure is
arbitrary, and the natural-number equalities transport only the large-rank types. -/
def UnequalRankAdjacentBlockSpanStatement (n r : ℕ) : Prop :=
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
  n < r →
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
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

end Langlands.RankinSelberg
