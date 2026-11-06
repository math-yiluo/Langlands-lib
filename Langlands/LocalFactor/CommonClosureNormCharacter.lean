import Langlands.LocalField.Normalization.ComplexCharacter
import Langlands.LocalFactor.NonabelianDualityReduction
import Langlands.Weil.Representation.CharacterLineDual

/-! # Normalized reciprocity and actual norm-twisted character duality -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Supplied normalized reciprocity pulls the field's normalized absolute
value back to the actual common-closure Weil norm. -/
theorem weilCharacter_normalizedAbsCharacter
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e) (E : Extension F) :
    weilCharacter F e E ((fieldData F E).normalizedAbsCharacter) =
      CommonClosureWeilDeligne.normCharacter F E := by
  apply ContinuousMonoidHom.ext
  intro w
  apply Units.ext
  rw [CommonClosureWeilDeligne.normCharacter_apply]
  change ((fieldData F E).normalizedAbs
      ((reciprocityUnits F e E w : E.fieldˣ) : E.field) : ℂ) = _
  have h := he.2 E (LocalClassField.abelianizationProjection (weilSubgroup F E) w)
  change (fieldData F E).normalizedAbs
      ((reciprocityUnits F e E w : E.fieldˣ) : E.field) =
    (F.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-(CommonClosureSpectral.baseDegree F E w).toAdd) at h
  rw [h, Complex.ofReal_zpow]
  rfl

/-- The norm-twisted full contragredient of a field-character class is the
class of normalized absolute value times the inverse field character. -/
theorem normTwistedDual_characterClass
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e) (E : Extension F)
    (χ : FieldCharacter F E) :
    letI := (fieldData F E).topology
    ExactGrothendieckGroup.continuousTwistedDual
        (CommonClosureWeilDeligne.normCharacter F E)
        (characterClass.{uF, uV} F e E χ) =
      characterClass.{uF, uV} F e E
        ((fieldData F E).normalizedAbsCharacter * χ⁻¹) := by
  let := (fieldData F E).topology
  change ExactGrothendieckGroup.continuousTwist
      (CommonClosureWeilDeligne.normCharacter F E)
      (ExactGrothendieckGroup.continuousDual
        (ExactGrothendieckGroup.characterClass (weilCharacter F e E χ))) = _
  rw [ExactGrothendieckGroup.continuousTwist_continuousDual_characterClass,
    ← weilCharacter_normalizedAbsCharacter F e he E]
  rfl

end Langlands.LocalFactor.CommonClosure
