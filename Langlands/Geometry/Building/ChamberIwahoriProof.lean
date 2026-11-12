import Langlands.Geometry.Building.ChamberIwahoriFactorPairReduction
import Langlands.Geometry.Building.KPMinimalLeviZeroComparisonProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of the full and sharp chamber Iwahori decompositions

KP 7.4.1, 7.4.3, 7.4.4 and 7.4.9 with the fixed-sign bijections of 7.3.12(3),(5), for every
actual datum `P`. The published factor-pair reduction
`chamberIwahoriDecomposition_of_hasOppositeFactorPairs` is applied with both of its inputs
discharged by published proofs: opposite factor pairs come from the rank-one factorization
(KP 2.11.17), and the cover-image containment comes from KP Corollary 2.6.28.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual torus `P.i` has opposite factor pairs, by the published
rank-one factorization (KP 2.11.17). -/
theorem hasOppositeFactorPairs : RelativeRoot.HasOppositeFactorPairs P.i := by
  have hG := P.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  exact (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs P.i hS).mp
    (rootRankOneFactorization F G hG P.S P.i P.isMaximalSplitTorus)

/-- The full and sharp chamber Iwahori decompositions, from KP Corollary 2.6.28
for the actual zero datum of `P`. -/
theorem chamberIwahoriDecomposition_of_centralizerZeroIntersection
    (hZ : P.zeroDatum.CentralizerZeroIntersectionStatement) :
    P.ChamberIwahoriDecompositionStatement :=
  P.chamberIwahoriDecomposition_of_hasOppositeFactorPairs P.hasOppositeFactorPairs
    (P.zeroDatum.coverImageCentralizerNormKernel_of_intersection hZ)

/-- **KP 7.4.9 with its full-parahoric consequences.** For every actual datum `P`, the full
and sharp chamber Iwahori decompositions hold, at both chamber depths and for every face of
the chamber satisfying the positive-system condition. -/
theorem chamberIwahoriDecomposition : P.ChamberIwahoriDecompositionStatement :=
  P.chamberIwahoriDecomposition_of_centralizerZeroIntersection
    (ZeroSubgroupDatum.minimalLeviZeroComparison P.zeroDatum).2

end Langlands.Geometry.Building.ParahoricBuildingData
