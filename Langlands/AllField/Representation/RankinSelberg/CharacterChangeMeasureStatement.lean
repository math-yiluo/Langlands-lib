import Langlands.Representation.RankinSelberg.CharacterChangeMeasureStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Canonical character-change quotient Haar measure law

The proposition below specializes the published measure-law property to the
actual local-field topology, normalized absolute value, and compatible quotient
measures for the actual normalized Haar measures. It does not prove that law.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- For every p-adic field with its supplied topological data, character change
pushes every compatible quotient measure forward by the positive-root modulus.
Unipotent right invariance is supplied by its published theorem, not assumed. -/
def CharacterChangeCompatibleMeasureStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ) (a : Fˣ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ

end Langlands.AllField.RankinSelberg
