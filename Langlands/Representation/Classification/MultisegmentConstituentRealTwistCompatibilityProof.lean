import Langlands.Representation.Classification.MultisegmentConstituentCharacterTwistCompatibilityProof

/-!
# Real determinant twists of multisegment constituents

The real twist `ν^s = |det|^s` is the character twist by `|·|^s` composed with the
determinant, so the proved character-twist compatibility gives the real one.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Real norm twists preserve and reflect the multisegment socle and head relations. -/
theorem multisegmentConstituentRealTwistCompatibility :
    MultisegmentConstituentRealTwistCompatibility.{uF, uV} F T := by
  let := T.topology
  intro n hn a s π
  have hχ : IsOpen ((realPowerCharacter T.normalizedAbsUnits s).ker : Set F.Carrierˣ) := by
    let := T.valuativeRel
    let := T.localField
    exact Subgroup.isOpen_mono (ker_le_realPowerCharacter_ker T.normalizedAbsUnits s)
      T.isOpen_ker_normalizedAbsUnits
  exact multisegmentConstituentCharacterTwistCompatibility.{uF, uV} F T
    (realPowerCharacter T.normalizedAbsUnits s) hχ n hn a π

end Langlands.Classification
