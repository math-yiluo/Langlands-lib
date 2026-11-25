import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.ValuationAffineRootSystems
import Langlands.Geometry.Building.ValuationDerivativeAffineRoots
import Langlands.Geometry.Building.ValuationBuildingTopologyCompatible
import Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslationProof
import Langlands.Geometry.Building.SimplyConnectedApartmentWeylAction
import Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly
import Langlands.Geometry.Building.ValuationQuasiSplitAdjointTranslation

/-! # The apartment axioms of valuation building data, assembled -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- V 6, V 7 and AS 2–AS 5 for `B`, from `SimplyConnectedFacetFixingStatement`, which gives the
simply connected sentence of AS 5. -/
theorem satisfiesApartmentAxioms_of_facetFixing
    (hfix : SimplyConnectedFacetFixingStatement.{u}) :
    B.SatisfiesApartmentAxioms := by
  obtain ⟨h2, h2', h3, -, h4, hW, hle⟩ := valuationBuildingAffineRootSystems.{u} F G B
  exact
    { omegaCompatible := B.isOmegaCompatible
      topologyCompatible := B.isTopologyCompatible
      isAffineRootSystem_extendedAffineRoots := h2
      derivativeRoots_extendedAffineRoots := h2'
      isAffineRootSystem_affineRoots := h3
      derivativeRoots_affineRoots :=
        ValuationBuildingData.derivativeRoots_affineRoots_of_isTopologyCompatible
          B.isTopologyCompatible
      mem_or_two_smul_mem := h4
      affineWeylGroup_le_range := hW
      range_le_extendedAffineWeylGroup := hle
      range_eq_affineWeylGroup_of_isSimplyConnected := fun hsc =>
        B.normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing
          hfix hsc h3 B.hasOppositeFactorPairs
      range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint := fun hqs had =>
        B.range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation
          valuationBuildingQuasiSplitAdjointTranslation hW hle hqs had }

end ValuationBuildingData

/-- `SimplyConnectedFacetFixingStatement` implies the apartment axioms V 6, V 7 and AS 2–AS 5
for all valuation building data over nonarchimedean local fields. -/
theorem valuationBuildingApartmentAxioms_of_facetFixing
    (hfix : SimplyConnectedFacetFixingStatement.{u}) :
    ValuationBuildingApartmentAxiomsStatement.{u} :=
  fun _ _ _ _ _ _ _ B => B.satisfiesApartmentAxioms_of_facetFixing hfix

end Langlands.Geometry.Building
