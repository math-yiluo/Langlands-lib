import Langlands.Geometry.Building.DerivedCoverSourceData
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusProof
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof

/-! # `N(F) ∩ G(F)^♮` acts through `W(Ψ)`, from facet fixing and the split-torus product

The range part of KP Theorem 7.5.3(2) follows from two published but unproved statements:
`SimplyConnectedFacetFixingStatement` and `DerivedCentralSplitTorusProductStatement`. All other
inputs of the derived-cover comparison are proved Library theorems.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Every nonidentity rational point of an actual relative-root group of the maximal split
torus of `B` has an opposite factor pair, by the proved rank-one factorization. -/
theorem hasOppositeFactorPairs (B : ValuationBuildingData G) :
    RelativeRoot.HasOppositeFactorPairs B.i :=
  fun a ha x hx hx1 =>
    (rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
      a ha x hx hx1).1.exists

end ValuationBuildingData

/-- KP Theorem 7.5.3(2), range part, follows from pointwise fixing of facets by their
stabilizers in the normalizer for simply connected groups
(`SimplyConnectedFacetFixingStatement`) and from the central isogeny `S_D × A → S` given by a
derived maximal split torus and a central split component
(`DerivedCentralSplitTorusProductStatement`). -/
def SimplyConnectedNormalizerAffineWeylReductionStatement : Prop :=
  SimplyConnectedFacetFixingStatement.{u} → DerivedCentralSplitTorusProductStatement.{u} →
    SimplyConnectedNormalizerAffineWeylStatement.{u}

/-- The derived-cover comparison of `DerivedCoverSourceData` proves the reduction; its
remaining inputs are the proved split-torus, centralizer-comparison and rank-one theorems. -/
theorem simplyConnectedNormalizerAffineWeylReduction :
    SimplyConnectedNormalizerAffineWeylReductionStatement.{u} := by
  intro hfix hproduct F _ _ _ _ G _ P hA
  have : IsAffineHom P.zeroDatum.C.X.hom :=
    P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  exact (P.derivedCoverSourceData simplyConnectedDerivedCoverSplitTorus hproduct
      Cartan.centralizerValuationComparison).normalizer_map_eq_affineWeylGroup hfix
    (ValuationBuildingData.hasOppositeFactorPairs _) hA
    (ValuationBuildingData.hasOppositeFactorPairs _)

end Langlands.Geometry.Building
