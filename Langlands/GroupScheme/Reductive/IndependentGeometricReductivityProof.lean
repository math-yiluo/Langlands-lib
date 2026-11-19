import Langlands.GroupScheme.Reductive.IndependentHaboushReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellIndependentInputs
import Langlands.GroupScheme.Reductive.OppositeFactorPairsFromStructuralStatements
import Langlands.GroupScheme.Reductive.RankOneRootReducednessFromCentralCover
import Langlands.GroupScheme.Reductive.RootDatumFromRankOneReducedness
import Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction
import Langlands.GroupScheme.Reductive.IndependentRootCellReduction
import Langlands.GroupScheme.Reductive.RootLieLineRankOneReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof

/-! # Geometric reductivity from the rank-one central cover

The unchanged `ReductiveGeometricReductivityStatement` (Haboush's theorem) is proved from the
rank-one `SL₂ × C` central cover `rankOneCentralCover`. The root datum, the rank-one root
cells, the root Lie lines, the coroot span and the opposite factor pairs are all derived
from that cover. They feed the Steinberg big-cell assembly and the split-cover assembly of
`IndependentHaboushReduction`. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IndependentHaboush

/-- Split root Lie spaces are lines, given the rank-one central cover. The rank-one case
comes from the support lines of the cover, and the general case from
`splitRootLieLine_of_rankOne` with connected reductive cocharacter centralizers. -/
theorem splitRootLieLine_of_centralCover (hcover : RankOneCentralCoverStatement.{u}) :
    SplitRootLieLineStatement.{u} := by
  have hRD : RootDatumExistenceStatement.{u} :=
    rootDatumExistence_of_rankOneReducedness (rankOneRootReducedness_of_centralCover hcover)
  have hs : SplitRankOneRootSupportLinesStatement.{u} :=
    splitRankOneRootSupportLines_of_algClosed
      (algClosedRankOneRootSupportLines_of_centralCover hcover)
  refine splitRootLieLine_of_rankOne dynamicCentralizerReductive ?_
  intro k _ G hG T hT i hi hdep χ hχ
  have := hG.isAffineHom
  obtain ⟨J, _, P, hP, -⟩ := hRD k G hG T hT i hi
  have hχ' : χ ∈ Set.range P.root := hP.2.1 ▸ hχ
  obtain ⟨r, rfl⟩ := hχ'
  exact (hs k G hG T hT i hi J P hP hdep r).2.1

/-- Geometric reductivity from the rank-one central cover. The cover gives the root datum,
the root cells and the root lines; these give the coroot span, the opposite factor pairs and
the Steinberg big cell, and the root datum with the big cell gives the target. -/
theorem reductiveGeometricReductivity_of_centralCover
    (hcover : RankOneCentralCoverStatement.{u}) :
    ReductiveGeometricReductivityStatement.{u} := by
  have hRD : RootDatumExistenceStatement.{u} :=
    rootDatumExistence_of_rankOneReducedness (rankOneRootReducedness_of_centralCover hcover)
  have hcell : SplitRankOneRootCellStatement.{u} := splitRankOneRootCell_of_centralCover hcover
  have hline : SplitRootLieLineStatement.{u} := splitRootLieLine_of_centralCover hcover
  exact reductiveGeometricReductivity_of_rootDatum_and_bigCell hRD
    (IndependentSteinbergInputs.to_statement
      ⟨hRD, hcell, hline,
        splitSimplyConnectedCorootSpan_of_corootSpanLineInputs ⟨hRD, hcell, hline⟩,
        algClosedOppositeFactorPairs_of_structuralStatements hRD hcell hline⟩)

/-- **Haboush's theorem** (geometric reductivity of connected reductive groups over an
algebraically closed field, in every characteristic), proved through the rank-one central
cover. -/
theorem reductiveGeometricReductivity : ReductiveGeometricReductivityStatement.{u} :=
  reductiveGeometricReductivity_of_centralCover rankOneCentralCover

end Langlands.GroupScheme.IndependentHaboush
