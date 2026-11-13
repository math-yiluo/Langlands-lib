import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionStatement
import Langlands.Geometry.Building.BuildingComparisonAxiomProof
import Langlands.Geometry.Building.IsomorphismCompatibilityAxiomProof

/-! # Proof: Bruhat–Tits availability from the one-group clauses of corrected Definition 4.1.26 -/

universe u

namespace Langlands.Geometry.Building

/-- **Bruhat–Tits availability from the one-group clauses.** If every connected reductive group
over every nonarchimedean local field in universe `u` carries data satisfying the clauses of
corrected KP Definition 4.1.26 for the group alone, then the assignment choosing such data for
every group satisfies all ten corrected axioms: the comparisons between groups hold for
arbitrary supplied data by `buildingComparisonAxiom` and `isomorphismCompatibilityAxiom`. -/
theorem bruhatTitsAvailabilityReduction : BruhatTitsAvailabilityReductionStatement.{u} := by
  intro h
  refine ⟨⟨fun F _ _ _ _ G _ hG => Classical.choose (h F G hG)⟩, ?_⟩
  intro F _ _ _ _ G _ hG
  obtain ⟨hcentral, hderived, hcover⟩ := buildingComparisonAxiom.{u} F
  refine KPBuildingAssignment.isAvailableFor_iff.mpr
    ⟨Classical.choose_spec (h F G hG), ?_, ?_, ?_, ?_⟩
  · intro G' _ hG' f hf
    exact hcentral G G' f hf _ _
  · intro Gder _ hder d hd
    exact hderived G Gder d hd _ _
  · intro Gder Gsc _ hsc d π hπ
    exact hcover G Gder Gsc d π hπ _ _
  · intro F₂ _ _ _ _ σ hσ G₂ _ hG₂ fG
    exact isomorphismCompatibilityAxiom F F₂ σ hσ G G₂ fG _ _

end Langlands.Geometry.Building
