import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.BuildingFacetPartition

/-! # Closed facets of the actual valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The combinatorial closed facet, the union of all its incident lower facets.
Its identification with the affine-root closure in a chart is proved below. -/
def buildingFacetClosure (Fc : BuildingFacet B) : Set B.ReducedBuilding :=
  {x | ∃ Fd : BuildingFacet B, FacetPrecedes B Fd Fc ∧ x ∈ Fd.val}

@[simp]
theorem mem_buildingFacetClosure (Fc : BuildingFacet B) (x : B.ReducedBuilding) :
    x ∈ B.buildingFacetClosure Fc ↔
      ∃ Fd : BuildingFacet B, FacetPrecedes B Fd Fc ∧ x ∈ Fd.val := Iff.rfl

/-- Each facet is contained in its combinatorial closure. -/
theorem subset_buildingFacetClosure (Fc : BuildingFacet B) :
    Fc.val ⊆ B.buildingFacetClosure Fc :=
  fun _ hx => ⟨Fc, facetPrecedes_refl B Fc, hx⟩

/-- A combinatorial closed facet stays in every apartment containing its facet. -/
theorem buildingFacetClosure_subset_apartment
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B)
    (g : rationalPoints G) (hFc : Fc.val ⊆ g • B.apartmentImage) :
    B.buildingFacetClosure Fc ⊆ g • B.apartmentImage := by
  rintro x ⟨Fd, hDF, hx⟩
  exact B.subset_apartment_of_facetPrecedes hD hDF g hFc hx

/-- Membership of the combinatorial closure is incidence of the unique
containing facet of a point. -/
theorem mem_buildingFacetClosure_iff_facetPrecedes
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) (x : B.ReducedBuilding) :
    x ∈ B.buildingFacetClosure Fc ↔ FacetPrecedes B (B.buildingFacetAt x) Fc := by
  constructor
  · rintro ⟨Fd, hDF, hx⟩
    rwa [(B.buildingFacetAt_eq_iff_mem hD x Fd).mpr hx]
  · intro h
    exact ⟨B.buildingFacetAt x, h, B.mem_buildingFacetAt x⟩

/-- Any one point of a facet in a closed facet forces the whole face incidence. -/
theorem facetPrecedes_iff_nonempty_inter_buildingFacetClosure
    (hD : B.SatisfiesApartmentAxioms) (Fc Cc : BuildingFacet B) :
    FacetPrecedes B Fc Cc ↔ (Fc.val ∩ B.buildingFacetClosure Cc).Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Fc.property.nonempty
    exact ⟨x, hx, Fc, h, hx⟩
  · rintro ⟨x, hx, Fd, hDC, hxd⟩
    have heq : Fc = Fd := Subtype.ext (Fc.property.eq_of_mem_mem B hD Fd.property hx hxd)
    exact heq ▸ hDC

/-- The face relation is exactly containment in the combinatorial closed facet. -/
theorem facetPrecedes_iff_subset_buildingFacetClosure
    (hD : B.SatisfiesApartmentAxioms) (Fc Cc : BuildingFacet B) :
    FacetPrecedes B Fc Cc ↔ Fc.val ⊆ B.buildingFacetClosure Cc := by
  constructor
  · exact fun h _ hx => ⟨Fc, h, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Fc.property.nonempty
    exact (B.facetPrecedes_iff_nonempty_inter_buildingFacetClosure hD Fc Cc).mpr
      ⟨x, hx, h hx⟩

/-- The union of all incident lower facets is exactly the image of the affine
facet closure in any presentation of its upper facet. This requires no chart
injectivity or opposite-factor pairs. -/
theorem buildingFacetClosure_eq_image
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B)
    (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetClosure Fc =
      B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots a := by
  apply Set.Subset.antisymm
  · rintro _ ⟨Fd, ⟨h, Fa, Ca, hFace, hFd, hFc'⟩, hx⟩
    have hapoint : B.translatedApartmentMap g a ∈ Fc.val := by
      rw [hFc]
      exact ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩
    rw [hFc'] at hapoint
    obtain ⟨c, hc, hca⟩ := hapoint
    change h • B.apartmentMap c = g • B.apartmentMap a at hca
    have hca' : (g⁻¹ * h) • B.apartmentMap c = B.apartmentMap a := by
      rw [mul_smul, hca, inv_smul_smul]
    obtain ⟨n, hn, heq⟩ :=
      B.exists_normalizer_eq_on_translated_facetClosure hD (g⁻¹ * h) hca'
    rw [hFd] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc := B.apartment.mem_facetClosure_of_isFaceOf hFace hc hy
    have hyna : n • y ∈ AffineRootSystem.facetClosure B.affineRoots a := by
      rw [← hn]
      intro ψ hψ
      exact hyc _ ((AffineRootSystem.comp_mem_iff
        (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1 ψ).mpr hψ)
    refine ⟨n • y, hyna, ?_⟩
    have H := congrArg (g • ·) (heq y hyc)
    change g • B.apartmentMap (n • y) = h • B.apartmentMap y
    have H' : h • B.apartmentMap y = g • B.apartmentMap (n • y) := by
      simpa only [mul_smul, smul_inv_smul] using H
    exact H'.symm
  · rintro _ ⟨y, hy, rfl⟩
    let Fd : BuildingFacet B :=
      ⟨B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots y,
        ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩
    refine ⟨Fd, ?_, y, AffineRootSystem.mem_facet_self _ _, rfl⟩
    exact ⟨g, _, _, ⟨AffineRootSystem.isFacet_facet _ _, a, rfl,
      AffineRootSystem.facet_subset_facetClosure_iff.mpr hy⟩, rfl, hFc⟩

/-- On a translated apartment, the closed facet through a point has the exact
original affine-root closure as its coordinate description. -/
theorem buildingFacetClosure_at_translatedApartmentMap
    (hD : B.SatisfiesApartmentAxioms) (g : rationalPoints G) (a : B.Apartment) :
    B.buildingFacetClosure (B.buildingFacetAt (B.translatedApartmentMap g a)) =
      B.translatedApartmentMap g '' AffineRootSystem.facetClosure B.affineRoots a :=
  B.buildingFacetClosure_eq_image hD _ g a (B.buildingFacetAt_translatedApartmentMap hD g a)

/-- Incidence gives inclusion of the corresponding closed facets. -/
theorem buildingFacetClosure_mono
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    {Fc Cc : BuildingFacet B} (hFC : FacetPrecedes B Fc Cc) :
    B.buildingFacetClosure Fc ⊆ B.buildingFacetClosure Cc := by
  rintro _ ⟨Fd, hDF, hx⟩
  exact ⟨Fd, B.facetPrecedes_trans hD hinj hDF hFC, hx⟩

/-- Inclusion of closed facets recovers exactly the existing face relation. -/
theorem facetPrecedes_iff_buildingFacetClosure_subset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Cc : BuildingFacet B) :
    FacetPrecedes B Fc Cc ↔ B.buildingFacetClosure Fc ⊆ B.buildingFacetClosure Cc := by
  refine ⟨B.buildingFacetClosure_mono hD hinj, fun h => ?_⟩
  exact (B.facetPrecedes_iff_subset_buildingFacetClosure hD Fc Cc).mpr
    ((B.subset_buildingFacetClosure Fc).trans h)

/-- A closed facet determines its original open facet. -/
theorem buildingFacetClosure_injective
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap) :
    Function.Injective B.buildingFacetClosure := by
  intro Fc Cc hFC
  apply B.facetPrecedes_antisymm hD hinj
  · exact (B.facetPrecedes_iff_buildingFacetClosure_subset hD hinj Fc Cc).mpr hFC.subset
  · exact (B.facetPrecedes_iff_buildingFacetClosure_subset hD hinj Cc Fc).mpr hFC.symm.subset

/-- Embed the original facets into subsets of the same reduced quotient by
taking the union of their faces. The preceding theorem identifies incidence
with inclusion on these images. -/
def buildingFacetClosureEmbedding
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap) :
    BuildingFacet B ↪ Set B.ReducedBuilding :=
  ⟨B.buildingFacetClosure, B.buildingFacetClosure_injective hD hinj⟩

end Langlands.Geometry.Building.ValuationBuildingData
