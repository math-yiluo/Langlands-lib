import Langlands.Geometry.Building.ChamberIwahoriReduction
import Langlands.Geometry.Building.ChamberSharpCore
import Langlands.Geometry.Building.ChamberSharpFacet
import Langlands.Geometry.Building.ChamberExchange
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan

/-!
# The chamber Iwahori decompositions from their algebraic prerequisites

The sharp chamber decomposition `ValuationBuildingData.ChamberSharpDecompositionStatement`
holds for every actual valuation building datum once the two algebraic statements
`RelativeRoot.DynamicRootOrderedProductStatement` and `RootRankOneFactorizationStatement`
are available. Together with the published reduction `chamberIwahoriReduction`, the full
chamber Iwahori decomposition of a parahoric building datum `P` then follows from the
centralizer intersection `P.CentralizerParahoricIntersectionStatement` (KP Lemma 7.4.3).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The sharp chamber decomposition (KP Corollary 7.4.9 with 7.3.12(3),(5)) of an actual
valuation building datum, from the Dynamic ordered-product and rank-one factorization
statements. -/
theorem chamberSharpDecomposition_of_prerequisites
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hrankOne : RootRankOneFactorizationStatement.{u}) :
    B.ChamberSharpDecompositionStatement := by
  intro hD C x ν hC hx hν
  have hG := B.isConnectedReductive
  have hi := B.isMaximalSplitTorus
  have hT : IsSplitTorus B.S.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  have hfinite := hT.finite_relativeRoots B.i
  have hspan := relativeRootsRestrictedCharactersSpan F G hG B.S B.i hi
  have hrank := hrankOne F G hG B.S B.i hi
  have hsharp := B.apartment.chamberSharpConclusion_of_core hprod hG hi
    hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
    hD.mem_or_two_smul_mem hC hx
    (fun mu hmu => KPApartmentData.sharpFixer_subset_mul_of_mem_chamber hT hfinite hspan hrank
      hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
      hD.mem_or_two_smul_mem hC hx mu hmu) ν hν
  refine ⟨hsharp, fun Fa hFC hPos => ?_⟩
  exact B.apartment.chamberSharpFacetConclusion_of_chamberSharpConclusion
    hD.mem_or_two_smul_mem hD.isAffineRootSystem_affineRoots hC hFC hPos hx hsharp

end ValuationBuildingData

/-- For every actual parahoric building datum `P` over a nonarchimedean local field, the
Dynamic ordered-product statement, the rank-one factorization statement and the centralizer
intersection `P.CentralizerParahoricIntersectionStatement` (KP Lemma 7.4.3) imply the full
and sharp chamber Iwahori decompositions `P.ChamberIwahoriDecompositionStatement`. -/
def ChamberIwahoriPrerequisiteReductionStatement : Prop :=
  RelativeRoot.DynamicRootOrderedProductStatement.{u} →
    RootRankOneFactorizationStatement.{u} →
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
      P.CentralizerParahoricIntersectionStatement →
        P.ChamberIwahoriDecompositionStatement

theorem chamberIwahoriPrerequisiteReduction :
    ChamberIwahoriPrerequisiteReductionStatement.{u} := by
  intro hprod hrankOne F _ _ _ _ G _ P hcent
  exact chamberIwahoriReduction F G P
    (P.toValuationBuildingData.chamberSharpDecomposition_of_prerequisites hprod hrankOne) hcent

end Langlands.Geometry.Building
