import Langlands.Geometry.Building.TitsCommonFacetApartment
import Langlands.Geometry.Building.BuildingFacetVertices

/-! # Original quotient facets embed into their finite actual vertex sets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (hD : P.toValuationBuildingData.SatisfiesApartmentAxioms)
  (hinj : Function.Injective P.apartmentMap)

local notation "B" => P.toValuationBuildingData

local instance : DecidableEq P.ReducedBuilding := Classical.decEq _

include hT

/-- The full actual Tits comparison makes finite actual vertex containment
equivalent to the original facet incidence, for every pair of facets. -/
theorem facetPrecedes_iff_vertexFinset_subset (Fc Fd : BuildingFacet B) :
    FacetPrecedes B Fc Fd ↔
      P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fc ⊆
        P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fd := by
  obtain ⟨Y, ⟨g, rfl⟩, hFc, hFd⟩ := hT.exists_apartment_contains_facets Fc Fd
  exact P.toValuationBuildingData.facetPrecedes_iff_vertexFinset_subset_of_common_apartment
    hD hinj Fc Fd g hFc hFd

/-- The original quotient facets are determined by their entire finite sets
of original vertices. -/
theorem vertexFinset_eq_iff (Fc Fd : BuildingFacet B) :
    P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fc =
      P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fd ↔ Fc = Fd := by
  constructor
  · intro he
    exact P.toValuationBuildingData.facetPrecedes_antisymm hD hinj
      ((hT.facetPrecedes_iff_vertexFinset_subset hD hinj Fc Fd).mpr he.subset)
      ((hT.facetPrecedes_iff_vertexFinset_subset hD hinj Fd Fc).mpr he.symm.subset)
  · rintro rfl
    rfl

/-- The existing vertex encoding is injective on all original facets. -/
theorem vertexFinset_injective :
    Function.Injective (P.toValuationBuildingData.buildingFacetVertexFinset hD hinj) :=
  fun Fc Fd he => (hT.vertexFinset_eq_iff hD hinj Fc Fd).mp he

/-- Original facet incidence embeds as inclusion of the finite actual vertex
sets in the original valuation quotient. -/
def facetVertexOrderEmbedding :
    @OrderEmbedding (BuildingFacet B) (Finset P.ReducedBuilding)
      (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE inferInstance :=
  @OrderEmbedding.ofMapLEIff _ _
    (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj) inferInstance
    (P.toValuationBuildingData.buildingFacetVertexFinset hD hinj)
    (fun Fc Fd => (hT.facetPrecedes_iff_vertexFinset_subset hD hinj Fc Fd).symm)

@[simp] theorem facetVertexOrderEmbedding_apply (Fc : BuildingFacet B) :
    hT.facetVertexOrderEmbedding hD hinj Fc =
      P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fc := rfl

/-- The global order embedding uses the original rational-point action. -/
theorem facetVertexOrderEmbedding_translate (g : rationalPoints G) (Fc : BuildingFacet B) :
    hT.facetVertexOrderEmbedding hD hinj (P.toValuationBuildingData.facetTranslateEquiv g Fc) =
      (hT.facetVertexOrderEmbedding hD hinj Fc).image (g • ·) := by
  classical
  exact P.toValuationBuildingData.buildingFacetVertexFinset_translate hD hinj g Fc

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
