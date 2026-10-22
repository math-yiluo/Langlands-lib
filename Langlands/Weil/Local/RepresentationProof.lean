import Langlands.Weil.Local.ContinuityProof
import Langlands.Weil.Local.GaloisCorrectionProof
import Langlands.Weil.Local.IrreducibleReductionProof
import Langlands.Weil.Local.CharacterNormProof

/-! # The nine-clause structure aggregate for the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

/-- The nine published actual-local structure results, conjoined for every
prime and every finite p-adic field in the order of the statement. -/
theorem localWeilRepresentationStatements :
    LocalWeilRepresentationStatements.{u, v} := by
  intro p _ F
  exact ⟨localWeilContinuity.{u, v} F,
    localWeilGaloisTypeFor.{u, v} F,
    localWeilUnramifiedCorrectionFor.{u, v} F,
    localWeilIrreducibleReductionFor.{u, v} F,
    localUnramifiedCharacterClassificationFor.{u} F,
    localWeilCharacterNormalizationFor.{u, v} F,
    localCharacterInertia.{u} F,
    localNormFaithfulnessFor.{u} F,
    localFrobeniusHypothesesFor.{u} F⟩

-- Check the complete unapplied type, first at the named proposition and then
-- with its prime/field telescope and all nine conjuncts unfolded.
example : LocalWeilRepresentationStatements.{u, v} :=
  @localWeilRepresentationStatements.{u, v}

example : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    LocalWeilContinuityFor.{u, v} F ∧
    LocalWeilGaloisTypeFor.{u, v} F ∧
    LocalWeilUnramifiedCorrectionFor.{u, v} F ∧
    LocalWeilIrreducibleReductionFor.{u, v} F ∧
    LocalUnramifiedCharacterClassificationFor F ∧
    LocalWeilCharacterNormalizationFor.{u, v} F ∧
    LocalCharacterInertiaFor F ∧
    LocalNormFaithfulnessFor F ∧
    LocalFrobeniusHypothesesFor F :=
  @localWeilRepresentationStatements.{u, v}

end Langlands.Weil.Local
