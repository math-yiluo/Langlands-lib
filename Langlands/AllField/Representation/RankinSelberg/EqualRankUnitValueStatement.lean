import Langlands.Representation.RankinSelberg.EqualRankUnitValueStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# An actual equal-rank JPSS integral with rational value one

This proposition isolates the unit test of JPSS (1983), printed page 393,
with the full telescope of `EqualRankAnalyticStatement`. It asserts no proof
of the test-vector construction, Kirillov surjectivity, or general rationality.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankUnitValueStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Some actual coefficient vectors and Schwartz--Bruhat test function have
rational continuation equal to one. This includes rank one and possibly
reducible Whittaker-type representations, with every compatible quotient measure.
It is a proposition definition, not a proof or an added hypothesis of analyticity. -/
def EqualRankUnitValueStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
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
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          (1 : RationalFunctions) ∈ equalRankRationalValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ π σ ℓ ℓ'

end Langlands.AllField.RankinSelberg
