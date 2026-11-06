import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.Geometry.Building.ValuationBuildingMetricAssembly
import Langlands.Geometry.Building.ValuationBuildingDistance
import Langlands.Geometry.Building.ValuationBuildingRetraction

/-! # The complete NPC metric on the existing KP quotient

KP Section 4.2: the distance `buildingDist`, computed in common apartments,
together with the retractions `ρ_{A,C}`, satisfies the hypotheses of the
metric assembly, which yields a metric realization of `B(G)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Section 4.2 (Propositions 4.2.1, 4.2.3, 4.2.7 and Theorem 4.2.10): the
existing quotient carries a complete NPC metric for which `G(F)` acts
isometrically with continuous orbit maps. -/
theorem metricRealization : MetricRealizationStatement.{u} := by
  apply ValuationBuildingData.metricRealizationStatement_of_exists_isRetractionBuildingDistance
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro P R T hR hB hT hRR hD hC hTits
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨y, hy, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary P.Apartment)
  obtain ⟨W, _, π, Sgen, hTy⟩ := hTits _ ⟨y, hy, rfl⟩
  have hN := hR.normalizerApartmentStabilizer
  have hK := hR.isBuilding
  exact ⟨P.toValuationBuildingData.buildingDist R hK,
    { smul := P.buildingDist_smul hD hN hC hTy R hK
      apartmentMap := P.buildingDist_apartmentMap hD hN hC hTy R hK
      exists_retraction := P.exists_apartmentRetraction
        (R.hasCommonApartmentWith_of_isBuilding hK) hD hN hC hTits
        (P.buildingDist_translatedApartmentMap hD hN hC hTy R hK) }⟩

end Langlands.Geometry.Building
