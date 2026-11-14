import Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Rectangular Haar measure under JPSS character change

These propositions state the positive-power pushforward law for the existing
inverse row scaling. They cover arbitrary rectangular additive Haar measures
and the actual JPSS product measure. They do not prove either measure law.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeRectangularHaarStatement CharacterChangeRectangularProductStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Inverse row scaling pushes every Borel rectangular additive Haar measure
forward by the existing positive character-change modulus. -/
def CharacterChangeRectangularHaarStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (j n : ℕ),
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
      [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
      (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
      [ν.IsAddHaarMeasure] (a : Fˣ),
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n ν

/-- The same law for the actual JPSS product of any shared scalar additive Haar
measure, with canonical scalar Borel and entrywise product measurable structures. -/
def CharacterChangeRectangularProductStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (j n : ℕ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.secondCountableTopology
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F) (a : Fˣ),
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n
        (rectangularMeasure η j (n + 1))

end Langlands.AllField.RankinSelberg
