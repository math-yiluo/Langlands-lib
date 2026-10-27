import Langlands.Representation.RankinSelberg.UnequalRankUnitSpanStatement
import Langlands.Representation.Whittaker.ModelKirillovStatement

/-!
# Compact mirabolic unit tests for every unequal-rank JPSS block

This internal proposition separates compact test construction from the
subsequent Kirillov lift in the unit-span argument of JPSS (1983),
printed pages 393–394. It does not prove the construction.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every unequal-rank block admits a compact mirabolic test function and an
actual smaller coefficient-model vector whose product integral converges and
equals one for every complex parameter. No large representation or Kirillov
lifting hypothesis is assumed. -/
def UnequalRankMirabolicUnitTestStatement (n j k : ℕ) : Prop :=
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
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W,
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

end Langlands.RankinSelberg
