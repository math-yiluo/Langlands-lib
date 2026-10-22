import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# Canonical character-change quotient Haar measure law

The proposition below specializes the published measure-law property to the
actual local-field topology, normalized absolute value, and compatible quotient
measures for the actual normalized Haar measures. It does not prove that law.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- For every p-adic field with its supplied topological data, character change
pushes every compatible quotient measure forward by the positive-root modulus.
Unipotent right invariance is supplied by its published theorem, not assumed. -/
def CharacterChangeCompatibleMeasureStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (a : F.Carrierˣ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ

end Langlands.RankinSelberg
