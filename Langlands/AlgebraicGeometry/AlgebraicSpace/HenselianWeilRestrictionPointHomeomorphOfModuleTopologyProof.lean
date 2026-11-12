import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionPointComparison

/-! # Corrected finite Weil restriction point homeomorphism -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

private theorem finiteTypeAtlasLocallyFiniteType
    {R : Type u} [CommRing R] {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (hft : FiniteTypeOverRing R X) : LocallyOfFiniteTypeOverBase X := by
  obtain ⟨U, a, ha, hs, hU⟩ := hft.exists_atlas
  exact ⟨U, a, ha, hs, hU.1⟩

/-- Conrad's Proposition 5.11(1), corrected by the module-topology hypothesis
from Example 2.4, including existence of the algebraic-space Weil restriction. -/
theorem henselianWeilRestrictionPointHomeomorphOfModuleTopology :
    HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement.{u} := by
  intro K K' _ _ _ _ _ hK hK' Y' hY'qs hY'ft
  obtain ⟨h, hYqs, hYft, _, _⟩ := spaceWeilRestriction K K' Y' hY'qs hY'ft
  refine ⟨h, ?_⟩
  exact isHomeomorph_ringWeilRestrictionBasePointsEquiv K K' Y' hK hK'
    ⟨hY'qs, finiteTypeAtlasLocallyFiniteType hY'ft⟩ h
    ⟨hYqs, finiteTypeAtlasLocallyFiniteType hYft⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
