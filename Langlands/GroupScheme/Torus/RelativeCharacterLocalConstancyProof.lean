import Langlands.GroupScheme.Torus.RelativeCharacterLocalConstancyStatement
import Langlands.GroupScheme.Torus.RelativeCharacterConstancyProof
import Langlands.GroupScheme.Cartier.RelativeHomSheaf

/-! # Actual characters of multiplicative-type groups form an étale local system -/

universe u

open CategoryTheory

namespace Langlands.GroupScheme

/-- The actual character presheaf of a multiplicative-type group is an étale sheaf
and is locally constant with finitely generated coefficients. -/
theorem relativeCharacterLocalConstancy : RelativeCharacterLocalConstancyStatement.{u} := by
  intro S H hH
  refine ⟨Cartier.isEtaleSheaf_characters hH.commGroupScheme, ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := multiplicativeTypeQuasiIsotrivial.1 S H hH
  refine ⟨𝒰, ?_⟩
  intro i
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    (relativeCharacterConstancy (𝒰.X i) _ (hH.baseChange (𝒰.f i))).1 (h𝒰 i)
  exact ⟨M, hM, ⟨Cartier.charactersBaseChangeIso hH.commGroupScheme (𝒰.f i) ≪≫ e⟩⟩

end Langlands.GroupScheme
