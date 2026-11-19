import Langlands.GroupScheme.Reductive.SteinbergBigCellStatement
import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof
import Langlands.GroupScheme.Reductive.RankOneRootReducednessFromCentralCover
import Langlands.GroupScheme.Reductive.RootDatumFromRankOneReducedness
import Langlands.GroupScheme.Reductive.IndependentRootCellReduction
import Langlands.GroupScheme.Reductive.RootLieLineFromCentralCover
import Langlands.GroupScheme.Reductive.OppositeFactorPairsFromStructuralStatements
import Langlands.GroupScheme.SimplyConnected.SplitCorootSpanLineReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellIndependentInputs

/-! # Steinberg big-cell data from the rank-one central cover -/

universe u

namespace Langlands.GroupScheme

/-- The exact Steinberg big-cell statement follows from the independent geometric
rank-one cover and its structural consequences. -/
theorem steinbergBigCellIndependent : SteinbergBigCellStatement.{u} := by
  have hcover : RankOneCentralCoverStatement.{u} := rankOneCentralCover
  have hRD := rootDatumExistence_of_rankOneReducedness
    (rankOneRootReducedness_of_centralCover hcover)
  have hcell := splitRankOneRootCell_of_centralCover hcover
  have hline := splitRootLieLine_of_centralCover hcover
  exact IndependentSteinbergInputs.to_statement
    { rootData := hRD
      rootCells := hcell
      rootLines := hline
      corootGeneration := splitSimplyConnectedCorootSpan_of_corootSpanLineInputs
        ⟨hRD, hcell, hline⟩
      oppositePairs := algClosedOppositeFactorPairs_of_structuralStatements hRD hcell hline }

end Langlands.GroupScheme
