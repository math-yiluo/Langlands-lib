import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterReduction
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof

/-! # Central split tori detect nonzero rational characters of connected reductive groups

A connected reductive group `G` over a field has a closed central torus `Z ⟶ G` whose product with
the derived subgroup `D ⟶ G` is an epimorphism of schemes onto `G`
(`reductiveCentralDerivedProduct_of_torusSurjectivity` applied to
`reductiveCentralTorusSurjectivity`). A rational character vanishes on `D`, so a nonzero character
is nonzero on `Z` (`IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`). The
reduction `centralSplitTorusCharacter_of_centralTorusCharacter` passes from this central torus to
a central split torus.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, every nonzero rational character of a connected reductive group restricts
to a nonzero character of some central split torus. -/
theorem centralSplitTorusCharacter : CentralSplitTorusCharacterStatement.{u} := by
  refine centralSplitTorusCharacter_of_centralTorusCharacter ?_
  intro k _ G hG χ hχ
  obtain ⟨Z, D, i, d, hAffine, hFiniteType, hTorus, hClosed, hCentral, hd, hEpi⟩ :=
    reductiveCentralDerivedProduct_of_torusSurjectivity reductiveCentralTorusSurjectivity k G hG
  have : Epi (subgroupProductMap i d) := hEpi
  exact ⟨Z, i, hAffine, hFiniteType, hTorus, hClosed, hCentral,
    hd.characterRestrict_ne_zero_of_epi_subgroupProductMap i χ hχ⟩

end Langlands.GroupScheme
