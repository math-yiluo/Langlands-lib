import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanStatement
import Langlands.AllField.Representation.Whittaker.ModelKirillovStatement
/-!
# Compact mirabolic unit tests for every unequal-rank JPSS block

This internal proposition separates compact test construction from the
subsequent Kirillov lift in the unit-span argument of JPSS (1983),
printed pages 393–394. It does not prove the construction.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding ModelKirillovTransferStatement
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uW

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Every unequal-rank block admits a compact mirabolic test function and an
actual smaller coefficient-model vector whose product integral converges and
equals one for every complex parameter. No large representation or Kirillov
lifting hypothesis is assumed. -/
def UnequalRankMirabolicUnitTestStatement (n j k : ℕ) : Prop :=
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
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W,
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ ℓ' : glInverseFunctionals ψ n σ, ℓ'.val ≠ 0 →
          ∃ φ : WhittakerFunctions ψ (n + (j + k + 1)),
          ∃ f' : (coefficientModel σ ℓ').toSubmodule,
            IsMirabolicTestFunction ψ (n + (j + k + 1)) φ ∧
            ∀ s : ℂ,
              UnequalRankConverges ψ (normalizedAbsoluteValue T) j k
                μ (rectangularMeasure ν j (n + 1)) φ f'.val s ∧
              unequalRankIntegral ψ (normalizedAbsoluteValue T) j k
                μ (rectangularMeasure ν j (n + 1)) φ f'.val s = 1

end Langlands.AllField.RankinSelberg
