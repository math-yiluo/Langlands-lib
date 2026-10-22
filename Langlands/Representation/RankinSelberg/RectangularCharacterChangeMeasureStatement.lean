import Langlands.Representation.RankinSelberg.UnequalRankCharacterIntegrals
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Rectangular Haar measure under JPSS character change

These propositions state the positive-power pushforward law for the existing
inverse row scaling. They cover arbitrary rectangular additive Haar measures
and the actual JPSS product measure. They do not prove either measure law.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

/-- Inverse row scaling pushes every Borel rectangular additive Haar measure
forward by the existing positive character-change modulus. -/
def CharacterChangeRectangularHaarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (j n : ℕ),
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
      [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F.Carrier)]
      (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
      [ν.IsAddHaarMeasure] (a : F.Carrierˣ),
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n ν

/-- The same law for the actual JPSS product of any shared scalar additive Haar
measure, with canonical scalar Borel and entrywise product measurable structures. -/
def CharacterChangeRectangularProductStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (j n : ℕ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ),
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n
        (rectangularMeasure η j (n + 1))

/-- The general rectangular Haar law together with its canonical JPSS product
specialization, as one exact target for a subsequent proof. -/
def CharacterChangeRectangularMeasureStatement : Prop :=
  CharacterChangeRectangularHaarStatement.{uF} ∧
    CharacterChangeRectangularProductStatement.{uF}

end Langlands.RankinSelberg
