import Langlands.Representation.RankinSelberg.UnequalRankUnitSpanStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Unit membership in every actual unequal-rank JPSS zeta span

This is the proposition target for the unit-span step in the proof of
JPSS Theorem 2.7, printed page 394. It does not prove that step.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The Laurent span of the actual unequal-rank rational continuations contains
one, for every allowed block and every supplied compatible measure. The hypotheses
are exactly those of `UnequalRankAnalyticStatement`; no analytic conclusion or
Kirillov restriction result is assumed. -/
def UnequalRankUnitSpanStatement (n j k : ℕ) : Prop :=
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
          (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType (n + (j + k + 1)) (standardCharacter ψ (n + (j + k + 1))) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ (n + (j + k + 1)) π)
          (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          (1 : RationalFunctions) ∈ zetaSpan
            (unequalRankRationalValues j k T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')

end Langlands.AllField.RankinSelberg
