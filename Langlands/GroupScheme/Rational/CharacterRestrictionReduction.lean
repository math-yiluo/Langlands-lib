import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterReduction
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CentralTorusCharacterStatement
import Langlands.GroupScheme.Reductive.CentralDerivedProductStatement
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Torus.CocharacterDetection
import Langlands.GroupScheme.Rational.SplitTorusImage

/-! # Reductions for restriction of rational characters to a split component

Restriction of rational characters to a split component is injective with finite-index range
once central split tori detect nonzero rational characters. Central split tori detect them once
central tori do, because cocharacters defined over `k` detect the rational characters of a torus
and the image of a cocharacter is a split subtorus. Central tori detect them once a central torus
and the derived subgroup generate the group.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- If a central torus and the derived subgroup generate every connected reductive group, central
tori detect nonzero rational characters. -/
theorem centralTorusCharacter_of_centralDerivedProduct
    (h : ReductiveCentralDerivedProductStatement.{u}) : CentralTorusCharacterStatement.{u} := by
  intro k _ G hG χ hχ
  obtain ⟨Z, D, i, d, hZa, hZf, hZ, hic, hcen, hd, hepi⟩ := h k G hG
  have : Epi (subgroupProductMap i d) := hepi
  exact ⟨Z, i, hZa, hZf, hZ, hic, hcen,
    hd.characterRestrict_ne_zero_of_epi_subgroupProductMap i χ hχ⟩

/-- If central split tori detect nonzero rational characters, restriction to every split
component of a connected reductive group is injective with finite-index range. -/
theorem characterRestriction_of_centralSplitTorusCharacter
    (h : CentralSplitTorusCharacterStatement.{u}) : CharacterRestrictionStatement.{u} := by
  intro k _ G hG A i hi
  exact ⟨characterRestrict_injective_of_centralSplitTorusCharacter h hG hi,
    hi.finiteIndex_range_characterRestrict hG⟩

/-- Surjectivity of the central-torus/derived-subgroup multiplication map gives the character
restriction statement. -/
theorem characterRestriction_of_torusSurjectivity
    (h : ReductiveCentralTorusSurjectivityStatement.{u}) : CharacterRestrictionStatement.{u} :=
  characterRestriction_of_centralSplitTorusCharacter
    (centralSplitTorusCharacter_of_centralTorusCharacter
      (centralTorusCharacter_of_centralDerivedProduct
        (reductiveCentralDerivedProduct_of_torusSurjectivity h)))

end Langlands.GroupScheme
