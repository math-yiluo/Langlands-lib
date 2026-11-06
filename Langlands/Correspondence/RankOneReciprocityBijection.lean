import Langlands.Correspondence.RankOneBijection
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers

/-!
# Actual rank-one correspondence along supplied reciprocity
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneReciprocityFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The actual rank-one continuous irreducible class of a field character
pulled back along the supplied reciprocity candidate. -/
def rankOneWeilCharacterClass (e : ReciprocityCandidate F) (χ : QuasiCharacter F) :
    IrreducibleWeilClass.{uF, uP} F 1 :=
  FiniteRepresentation.continuousIrreducibleCharacterClass
    (LocalFactor.RankOne.weilCharacter F e χ)

/-- The constructed Weil class realizes the existing scalar-character relation. -/
theorem rankOneWeilCharacterClass_spec (e : ReciprocityCandidate F)
    (χ : QuasiCharacter F) :
    IsRankOneWeilCharacter F (weilCharacter F e χ)
      (rankOneWeilCharacterClass.{uF, uP} F e χ) := by
  refine ⟨FiniteRepresentation.characterLine (weilCharacter F e χ), rfl, ?_⟩
  exact ⟨(FiniteRepresentation.characterLineEquiv (weilCharacter F e χ)).symm⟩

/-- Actual rank-one Weil character classes distinguish field characters. -/
theorem rankOneWeilCharacterClass_injective (e : ReciprocityCandidate F) :
    Function.Injective (rankOneWeilCharacterClass.{uF, uP} F e) := by
  intro χ η h
  apply weilCharacter_injective F e
  apply IsRankOneWeilCharacter.character_unique F
    (rankOneWeilCharacterClass_spec F e χ)
  rw [h]
  exact rankOneWeilCharacterClass_spec F e η

/-- Every actual rank-one Weil class is a pulled-back continuous field character. -/
theorem rankOneWeilCharacterClass_surjective (e : ReciprocityCandidate F) :
    Function.Surjective (rankOneWeilCharacterClass.{uF, uP} F e) := by
  intro σ
  obtain ⟨χ, hχ⟩ := exists_rankOneWeilFieldCharacter F e σ
  exact ⟨χ, IsRankOneWeilCharacter.class_unique F
    (rankOneWeilCharacterClass_spec F e χ) hχ⟩

/-- Continuous field characters classify actual rank-one Weil classes
along any supplied reciprocity candidate. -/
def rankOneWeilCharacterEquiv (e : ReciprocityCandidate F) :
    QuasiCharacter F ≃ IrreducibleWeilClass.{uF, uP} F 1 :=
  Equiv.ofBijective (rankOneWeilCharacterClass F e)
    ⟨rankOneWeilCharacterClass_injective F e, rankOneWeilCharacterClass_surjective F e⟩

/-- The actual rank-one Weil/supercuspidal bijection along supplied reciprocity. -/
def rankOneReciprocityEquiv (e : ReciprocityCandidate F) :
    IrreducibleWeilClass.{uF, uP} F 1 ≃ SupercuspidalAutomorphicClass.{uF, uA} F 1 :=
  (rankOneWeilCharacterEquiv F e).symm.trans (rankOneSupercuspidalCharacterEquiv F)

/-- The bijection sends each pulled-back character to its actual GL₁ class. -/
theorem rankOneReciprocityEquiv_character (e : ReciprocityCandidate F)
    (χ : QuasiCharacter F) :
    rankOneReciprocityEquiv.{uF, uP, uA} F e (rankOneWeilCharacterClass F e χ) =
      rankOneSupercuspidalClass F χ := by
  change (rankOneSupercuspidalCharacterEquiv F)
    ((rankOneWeilCharacterEquiv F e).symm ((rankOneWeilCharacterEquiv F e) χ)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Any representative of a pulled-back character has the required image. -/
theorem rankOneReciprocityEquiv_spec (e : ReciprocityCandidate F)
    (χ : QuasiCharacter F) (σ : IrreducibleWeilClass.{uF, uP} F 1)
    (hσ : IsRankOneWeilCharacter F (weilCharacter F e χ) σ) :
    IsSupercuspidalRankOneCharacter F χ (rankOneReciprocityEquiv.{uF, uP, uA} F e σ) := by
  have h := IsRankOneWeilCharacter.class_unique F hσ
    (rankOneWeilCharacterClass_spec F e χ)
  rw [h, rankOneReciprocityEquiv_character]
  exact rankOneSupercuspidalClass_spec F χ

/-- The endpoint rank-one condition is exactly agreement with this bijection. -/
theorem supercuspidalRankOneCompatibility_iff_eq (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) :
    SupercuspidalRankOneCompatibility F e c ↔
      c 1 = (rankOneReciprocityEquiv.{uF, uP, uA} F e : _ → _) := by
  constructor
  · intro hc
    funext σ
    obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F e σ
    obtain ⟨τ, hτ, hπ⟩ := hc χ
    have h := IsRankOneWeilCharacter.class_unique F hτ hσ
    subst τ
    exact IsSupercuspidalRankOneCharacter.class_unique F hπ
      (rankOneReciprocityEquiv_spec F e χ σ hσ)
  · intro hc χ
    refine ⟨rankOneWeilCharacterClass F e χ, rankOneWeilCharacterClass_spec F e χ, ?_⟩
    rw [hc, rankOneReciprocityEquiv_character]
    exact rankOneSupercuspidalClass_spec F χ

end Langlands.Correspondence
