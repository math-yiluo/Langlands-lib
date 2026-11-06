import Langlands.Group.TitsCommonApartment
import Langlands.Geometry.Building.TitsFacetApartmentTransport
import Langlands.Geometry.Building.CommonApartmentConstruction

/-! # Common apartments in the original quotient from its Tits comparison -/

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
include hT

/-- Two original facets lie in a common original translated apartment. -/
theorem exists_apartment_contains_facets (Fc Fd : BuildingFacet P.toValuationBuildingData) :
    ∃ Y : Set P.ReducedBuilding, P.IsApartment Y ∧ Fc.val ⊆ Y ∧ Fd.val ⊆ Y := by
  obtain ⟨a, haFc, haFd⟩ := hT.isTitsSystem.exists_common_restrictedApartment
    (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc))
    (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fd))
  have ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a ∈
      P.apartmentFacetStabilizers := by
    rw [hT.apartmentFacetStabilizers_eq]
    exact ⟨a, rfl⟩
  obtain ⟨g, hg⟩ := ha
  have hinj : Function.Injective P.facetZeroStabilizer :=
    fun _ _ he => hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _) he
  rw [hg] at haFc haFd
  obtain ⟨Fc', hFc', heFc⟩ := haFc
  obtain ⟨Fd', hFd', heFd⟩ := haFd
  exact ⟨g • P.apartmentImage, ⟨g, rfl⟩, (hinj heFc) ▸ hFc', (hinj heFd) ▸ hFd'⟩

/-- A chosen common apartment for the two original building facets. -/
def commonFacetApartment (Fc Fd : BuildingFacet P.toValuationBuildingData) :
    Set P.ReducedBuilding :=
  (hT.exists_apartment_contains_facets Fc Fd).choose

theorem commonFacetApartment_spec (Fc Fd : BuildingFacet P.toValuationBuildingData) :
    P.IsApartment (hT.commonFacetApartment Fc Fd) ∧
      Fc.val ⊆ hT.commonFacetApartment Fc Fd ∧ Fd.val ⊆ hT.commonFacetApartment Fc Fd :=
  (hT.exists_apartment_contains_facets Fc Fd).choose_spec

/-- Common apartments for arbitrary points, without an assumed geometric building. -/
theorem exists_apartment_mem_mem (x y : P.ReducedBuilding) :
    ∃ Y : Set P.ReducedBuilding, P.IsApartment Y ∧ x ∈ Y ∧ y ∈ Y := by
  obtain ⟨Fc, hx⟩ := P.toValuationBuildingData.exists_buildingFacet_mem x
  obtain ⟨Fd, hy⟩ := P.toValuationBuildingData.exists_buildingFacet_mem y
  obtain ⟨Y, hY, hFc, hFd⟩ := hT.exists_apartment_contains_facets Fc Fd
  exact ⟨Y, hY, hFc hx, hFd hy⟩

/-- The original common-apartment predicate follows from the full Tits comparison. -/
theorem hasCommonApartmentWith (x : P.ReducedBuilding) :
    P.toValuationBuildingData.HasCommonApartmentWith x :=
  fun y => hT.exists_apartment_mem_mem x y

/-- Every two facets of any supplied realization belong to one of its apartments. -/
theorem realization_exists_apartment_facets
    (R : P.toValuationBuildingData.PolysimplicialRealization) (Fc Fd : R.complex.facets) :
    ∃ 𝒜 ∈ R.apartments, Fc.val ∈ 𝒜 ∧ Fd.val ∈ 𝒜 := by
  obtain ⟨Y, hY, hFc, hFd⟩ := hT.exists_apartment_contains_facets (R.realize Fc) (R.realize Fd)
  exact ⟨R.apartmentComplex Y, ⟨Y, hY, rfl⟩, ⟨Fc.property, hFc⟩, ⟨Fd.property, hFd⟩⟩

/-- BL3 in the exact chamber form required by `AbstractBuilding.IsBuilding`. -/
theorem realization_exists_apartment
    (R : P.toValuationBuildingData.PolysimplicialRealization) :
    ∀ C D, AbstractBuilding.IsChamber R.complex.facets C →
      AbstractBuilding.IsChamber R.complex.facets D →
        ∃ 𝒜 ∈ R.apartments, C ∈ 𝒜 ∧ D ∈ 𝒜 := by
  intro C D hC hD
  exact hT.realization_exists_apartment_facets R ⟨C, hC.mem⟩ ⟨D, hD.mem⟩

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
