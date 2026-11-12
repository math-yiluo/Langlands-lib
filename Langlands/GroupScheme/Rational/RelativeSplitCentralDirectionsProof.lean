import Langlands.GroupScheme.Rational.SplitCentralDirectionsConstruction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.GroupScheme.Torus.CocharacterDetection
import Langlands.GroupScheme.Rational.SplitTorusImage

/-! # Actual split-component embeddings and full-lattice central directions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every nonzero rational character of a connected reductive group restricts to a
nonzero character of an actual central split torus. -/
private theorem centralSplitTorusCharacter_aux : CentralSplitTorusCharacterStatement.{u} := by
  intro k _ G hG χ hχ
  obtain ⟨Z, D, i, d, hZa, hZf, hZ, -, hcen, hd, hepi⟩ :=
    reductiveCentralDerivedProduct_of_torusSurjectivity reductiveCentralTorusSurjectivity k G hG
  have : Epi (subgroupProductMap i d) := hepi
  have hχi := hd.characterRestrict_ne_zero_of_epi_subgroupProductMap i χ hχ
  have : IsAffineHom Z.toGrp.X.hom := hZa
  have : LocallyOfFiniteType Z.toGrp.X.hom := hZf
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨φ, hφ⟩ := CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus hZ hχi
  obtain ⟨A, π, j, hj, hπj, hjc⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus isSplitTorus_gm (φ ≫ i)
  refine ⟨A, j, ⟨hj, hjc (hcen.comp φ)⟩, fun h0 => hφ ?_⟩
  rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, ← hπj, characterRestrict_comp,
    AddMonoidHom.comp_apply, h0, map_zero]

/-- Restriction of rational characters to every actual split component is injective with
finite-index range. -/
private theorem characterRestriction_aux : CharacterRestrictionStatement.{u} := by
  intro k _ G hG A i hi
  exact ⟨characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter_aux
    hG hi, hi.finiteIndex_range_characterRestrict hG⟩

/-- Every actual split component embeds into each maximal split torus with real cocharacter
image the common root annihilator, which has the rational-character rank and is fixed
pointwise by the actual relative Weyl group. -/
theorem relativeSplitCentralDirections : RelativeSplitCentralDirectionsStatement.{u} :=
  relativeSplitCentralDirections_of_centrality_characterRestriction rootAnnihilatorCentrality
    characterRestriction_aux

end Langlands.GroupScheme
