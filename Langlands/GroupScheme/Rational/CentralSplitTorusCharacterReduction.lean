import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterStatement
import Langlands.GroupScheme.Rational.CentralTorusCharacterStatement
import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Torus.CocharacterDetection

/-! # Central split tori detect characters if central tori do

A central homomorphism `φ : D ⟶ G` from a split torus into an affine group factors through a
central split subtorus of `G`, by `IsSplitTorus.exists_factor_isSplitSubtorus`; a character that is
nonzero on `φ` stays nonzero on that subtorus. A nonzero character of an affine, locally finite type
torus is nonzero on some cocharacter `𝔾_m ⟶ Z`, by
`CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus`. Together these reduce
`CentralSplitTorusCharacterStatement` to `CentralTorusCharacterStatement`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A rational character of an affine group `G` that is nonzero on a central homomorphism
`φ : D ⟶ G` from a split torus is nonzero on some central split torus of `G`: the closed image of
`φ`. -/
theorem exists_isCentralSplitTorus_characterRestrict_ne_zero {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {D : CommGroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D.toGrp)
    (φ : D.toGrp ⟶ G) (hφ : IsCentral φ) {χ : rationalCharacters G}
    (hχ : characterRestrict φ χ ≠ 0) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G),
      IsCentralSplitTorus i ∧ characterRestrict i χ ≠ 0 := by
  obtain ⟨A, π, i, hi, hπ, hc⟩ := IsSplitTorus.exists_factor_isSplitSubtorus hD φ
  refine ⟨A, i, ⟨hi, hc hφ⟩, fun h => hχ ?_⟩
  rw [← hπ, characterRestrict_comp, AddMonoidHom.comp_apply, h, map_zero]

/-- If central tori detect nonzero rational characters of connected reductive groups, so do
central split tori: a cocharacter of the central torus detects the restricted character, and the
closed image of that cocharacter is a central split torus. -/
theorem centralSplitTorusCharacter_of_centralTorusCharacter
    (h : CentralTorusCharacterStatement.{u}) : CentralSplitTorusCharacterStatement.{u} := by
  intro k _ G hG χ hχ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨Z, i, hAff, hLFT, hZ, -, hc, hne⟩ := h k G hG χ hχ
  obtain ⟨φ, hφ⟩ := CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus hZ hne
  refine exists_isCentralSplitTorus_characterRestrict_ne_zero isSplitTorus_gm (φ ≫ i)
    (hc.comp φ) ?_
  rwa [characterRestrict_comp, AddMonoidHom.comp_apply]

set_option linter.defProp false in
/-- The reduction of `CentralSplitTorusCharacterStatement` to `CentralTorusCharacterStatement`, as
a declaration whose type is the implication. -/
def centralSplitTorusCharacterOfCentralTorusCharacter :
    CentralTorusCharacterStatement.{u} → CentralSplitTorusCharacterStatement.{u} :=
  centralSplitTorusCharacter_of_centralTorusCharacter

end Langlands.GroupScheme
