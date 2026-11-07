import Langlands.Geometry.Building.AffineFacetIntersections
import Langlands.Geometry.Building.BuildingFacetCentroids
import Langlands.Geometry.Building.TitsCommonFacetApartment

/-! # Intersections of original closed facets in the valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance : DecidableEq B.ReducedBuilding := Classical.decEq _

/-- Two original closed quotient facets meet exactly when they share an
original quotient vertex. No global common-apartment comparison is needed. -/
theorem buildingFacetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Fd : BuildingFacet B) :
    (B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd).Nonempty ↔
      (B.buildingFacetVertexFinset hD hinj Fc ∩
        B.buildingFacetVertexFinset hD hinj Fd).Nonempty := by
  constructor
  · rintro ⟨x, hxc, hxd⟩
    have hxc' := (B.mem_buildingFacetClosure_iff_facetPrecedes hD Fc x).mp hxc
    have hxd' := (B.mem_buildingFacetClosure_iff_facetPrecedes hD Fd x).mp hxd
    obtain ⟨v, hv⟩ := B.buildingFacetVertexFinset_nonempty hD hinj (B.buildingFacetAt x)
    exact ⟨v, Finset.mem_inter.mpr
      ⟨B.buildingFacetVertexFinset_mono hD hinj hxc' hv,
        B.buildingFacetVertexFinset_mono hD hinj hxd' hv⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hvc, hvd⟩ := Finset.mem_inter.mp hv
    exact ⟨v, ((B.mem_buildingFacetVertexFinset hD hinj Fc v).mp hvc).1,
      ((B.mem_buildingFacetVertexFinset hD hinj Fd v).mp hvd).1⟩

attribute [local instance] metricRootFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- A nonempty intersection in one original injective chart is an original
closed quotient facet, represented by the centroid of the common affine vertices. -/
theorem exists_buildingFacetClosure_eq_inter_in_chart
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Fd : BuildingFacet B) (g : rationalPoints G) (a b : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a)
    (hFd : Fd.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots b)
    (hcd : (B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd).Nonempty) :
    ∃ Fe : BuildingFacet B,
      B.buildingFacetClosure Fe = B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd := by
  have hinter :
      B.translatedApartmentMap g ''
          (AffineRootSystem.facetClosure B.affineRoots a ∩
            AffineRootSystem.facetClosure B.affineRoots b) =
        B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd := by
    rw [Set.image_inter (B.translatedApartmentMap_injective hinj g),
      ← B.buildingFacetClosure_eq_image hD Fc g a hFc,
      ← B.buildingFacetClosure_eq_image hD Fd g b hFd]
  have hab : (AffineRootSystem.facetClosure B.affineRoots a ∩
      AffineRootSystem.facetClosure B.affineRoots b).Nonempty := by
    rw [← hinter] at hcd
    obtain ⟨_, y, hy, _⟩ := hcd
    exact ⟨y, hy⟩
  let c := AffineRootSystem.facetIntersectionCentroid hD.isAffineRootSystem_affineRoots a b
  refine ⟨B.buildingFacetAt (B.translatedApartmentMap g c), ?_⟩
  rw [B.buildingFacetClosure_at_translatedApartmentMap hD g c]
  change B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots
    (AffineRootSystem.facetIntersectionCentroid hD.isAffineRootSystem_affineRoots a b) = _
  rw [AffineRootSystem.facetClosure_facetIntersectionCentroid
    hD.isAffineRootSystem_affineRoots a b hab]
  exact hinter

/-- It suffices that both facets lie in a common original apartment. -/
theorem exists_buildingFacetClosure_eq_inter_of_common_apartment
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Fd : BuildingFacet B) (g : rationalPoints G)
    (hFc : Fc.val ⊆ g • B.apartmentImage) (hFd : Fd.val ⊆ g • B.apartmentImage)
    (hcd : (B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd).Nonempty) :
    ∃ Fe : BuildingFacet B,
      B.buildingFacetClosure Fe = B.buildingFacetClosure Fc ∩ B.buildingFacetClosure Fd := by
  obtain ⟨a, ha⟩ := B.exists_facet_presentation_in_apartment hD Fc g hFc
  obtain ⟨b, hb⟩ := B.exists_facet_presentation_in_apartment hD Fd g hFd
  exact B.exists_buildingFacetClosure_eq_inter_in_chart hD hinj Fc Fd g a b ha hb hcd

end ValuationBuildingData

namespace ParahoricBuildingData.IsBuildingTitsSystem

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}
  (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (hD : P.toValuationBuildingData.SatisfiesApartmentAxioms)
  (hinj : Function.Injective P.apartmentMap)

local notation "B" => P.toValuationBuildingData

local instance : DecidableEq P.ReducedBuilding := Classical.decEq _

include hT hD hinj

/-- The full actual Tits comparison makes every nonempty intersection of
original closed quotient facets another original closed quotient facet. -/
theorem exists_buildingFacetClosure_eq_inter (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty) :
    ∃ Fe : BuildingFacet B,
      P.toValuationBuildingData.buildingFacetClosure Fe = P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd := by
  obtain ⟨_, ⟨g, rfl⟩, hFc, hFd⟩ := hT.exists_apartment_contains_facets Fc Fd
  exact P.toValuationBuildingData.exists_buildingFacetClosure_eq_inter_of_common_apartment hD hinj
    Fc Fd g hFc hFd hcd

/-- The original facet whose original closure is the nonempty intersection.
The characterization below makes the choice unique. -/
def closedFacetIntersection (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty) :
    BuildingFacet B :=
  (hT.exists_buildingFacetClosure_eq_inter hD hinj Fc Fd hcd).choose

/-- The chosen facet has exactly the required original closed facet. -/
theorem buildingFacetClosure_closedFacetIntersection (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty) :
    P.toValuationBuildingData.buildingFacetClosure (hT.closedFacetIntersection hD hinj Fc Fd hcd) =
      P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd :=
  (hT.exists_buildingFacetClosure_eq_inter hD hinj Fc Fd hcd).choose_spec

/-- The actual vertices of the intersection are precisely the common original
quotient vertices. -/
theorem vertexFinset_closedFacetIntersection (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty) :
    P.toValuationBuildingData.buildingFacetVertexFinset hD hinj (hT.closedFacetIntersection hD hinj Fc Fd hcd) =
      P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fc ∩ P.toValuationBuildingData.buildingFacetVertexFinset hD hinj Fd := by
  ext x
  simp only [P.toValuationBuildingData.mem_buildingFacetVertexFinset, Finset.mem_inter,
    hT.buildingFacetClosure_closedFacetIntersection hD hinj Fc Fd hcd, Set.mem_inter_iff]
  tauto

/-- The intersection facet is the greatest common lower facet for the existing
original incidence relation. -/
theorem facetPrecedes_closedFacetIntersection_iff (Fc Fd Fe : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty) :
    FacetPrecedes B Fe (hT.closedFacetIntersection hD hinj Fc Fd hcd) ↔
      FacetPrecedes B Fe Fc ∧ FacetPrecedes B Fe Fd := by
  rw [P.toValuationBuildingData.facetPrecedes_iff_buildingFacetClosure_subset hD hinj,
    hT.buildingFacetClosure_closedFacetIntersection hD hinj Fc Fd hcd,
    Set.subset_inter_iff,
    ← P.toValuationBuildingData.facetPrecedes_iff_buildingFacetClosure_subset hD hinj,
    ← P.toValuationBuildingData.facetPrecedes_iff_buildingFacetClosure_subset hD hinj]

/-- Symmetry follows from the exact original closure characterization. -/
theorem closedFacetIntersection_comm (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty)
    (hdc : (P.toValuationBuildingData.buildingFacetClosure Fd ∩ P.toValuationBuildingData.buildingFacetClosure Fc).Nonempty) :
    hT.closedFacetIntersection hD hinj Fc Fd hcd =
      hT.closedFacetIntersection hD hinj Fd Fc hdc := by
  apply P.toValuationBuildingData.buildingFacetClosure_injective hD hinj
  rw [hT.buildingFacetClosure_closedFacetIntersection hD hinj Fc Fd hcd,
    hT.buildingFacetClosure_closedFacetIntersection hD hinj Fd Fc hdc, Set.inter_comm]

/-- Taking the intersection of a closed facet with itself recovers the original facet. -/
theorem closedFacetIntersection_self (Fc : BuildingFacet B)
    (hcc : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fc).Nonempty) :
    hT.closedFacetIntersection hD hinj Fc Fc hcc = Fc := by
  apply P.toValuationBuildingData.buildingFacetClosure_injective hD hinj
  rw [hT.buildingFacetClosure_closedFacetIntersection hD hinj Fc Fc hcc, Set.inter_self]

/-- The original rational-point action preserves the intersection facet. -/
theorem closedFacetIntersection_translate (g : rationalPoints G) (Fc Fd : BuildingFacet B)
    (hcd : (P.toValuationBuildingData.buildingFacetClosure Fc ∩ P.toValuationBuildingData.buildingFacetClosure Fd).Nonempty)
    (hcd' : (P.toValuationBuildingData.buildingFacetClosure (P.toValuationBuildingData.facetTranslateEquiv g Fc) ∩
      P.toValuationBuildingData.buildingFacetClosure (P.toValuationBuildingData.facetTranslateEquiv g Fd)).Nonempty) :
    hT.closedFacetIntersection hD hinj
        (P.toValuationBuildingData.facetTranslateEquiv g Fc) (P.toValuationBuildingData.facetTranslateEquiv g Fd) hcd' =
      P.toValuationBuildingData.facetTranslateEquiv g (hT.closedFacetIntersection hD hinj Fc Fd hcd) := by
  apply P.toValuationBuildingData.buildingFacetClosure_injective hD hinj
  rw [hT.buildingFacetClosure_closedFacetIntersection hD hinj _ _ hcd',
    P.toValuationBuildingData.buildingFacetClosure_translate, P.toValuationBuildingData.buildingFacetClosure_translate,
    P.toValuationBuildingData.buildingFacetClosure_translate,
    hT.buildingFacetClosure_closedFacetIntersection hD hinj Fc Fd hcd]
  exact (Set.image_inter (MulAction.injective g)).symm

end ParahoricBuildingData.IsBuildingTitsSystem

end Langlands.Geometry.Building
