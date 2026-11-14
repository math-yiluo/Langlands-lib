import Langlands.Geometry.Building.ValuationBuildingFacetEmbedding
import Langlands.Geometry.Building.FacetClosurePullback
import Langlands.Geometry.Building.BuildingFacetClosure

/-! # Facet incidence along an apartment-compatible building map -/

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
  {K : Type u} [Field K]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (C : IntegerValuationBuildingData v H)
  (φ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = φ g • e x)
  (hapt : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfacet : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

include hequiv hapt hfacet

/-- On any translated source apartment, the target closed facet cuts out
precisely the source affine-root closed facet. -/
theorem mem_buildingFacetClosure_image_chart_iff (g : rationalPoints G)
    (x y : B.Apartment) :
    e (B.translatedApartmentMap g y) ∈
        C.buildingFacetClosure (C.buildingFacetAt (e (B.translatedApartmentMap g x))) ↔
      y ∈ AffineRootSystem.facetClosure B.affineRoots x := by
  simp only [translatedApartmentMap, hequiv, hapt]
  change C.translatedApartmentMap (φ g) (a y) ∈
      C.buildingFacetClosure
        (C.buildingFacetAt (C.translatedApartmentMap (φ g) (a x))) ↔ _
  rw [C.buildingFacetClosure_at_translatedApartmentMap]
  have hcl := AffineRootSystem.preimage_facetClosure_of_preimage_facet
    a B.affineRoots C.affineRoots hfacet x
  constructor
  · rintro ⟨z, hz, heq⟩
    have hzy := C.translatedApartmentMap_injective C.apartmentMap_injective (φ g) heq
    subst z
    exact (Set.ext_iff.mp hcl y).mp hz
  · intro hy
    exact ⟨a y, (Set.ext_iff.mp hcl y).mpr hy, rfl⟩

variable (hD : B.SatisfiesApartmentAxioms) (hcommon : B.HasCommonApartments)

include hD hcommon

/-- Common source apartments globalize the exact closed-facet pullback. -/
theorem mem_buildingFacetClosure_image_iff (x y : B.ReducedBuilding) :
    e y ∈ C.buildingFacetClosure (C.buildingFacetAt (e x)) ↔
      y ∈ B.buildingFacetClosure (B.buildingFacetAt x) := by
  obtain ⟨g, p, q, rfl, rfl⟩ := hcommon x y
  change e (B.translatedApartmentMap g q) ∈
      C.buildingFacetClosure (C.buildingFacetAt (e (B.translatedApartmentMap g p))) ↔ _
  rw [mem_buildingFacetClosure_image_chart_iff B C φ e a hequiv hapt hfacet]
  change q ∈ AffineRootSystem.facetClosure B.affineRoots p ↔
    B.translatedApartmentMap g q ∈
      B.buildingFacetClosure (B.buildingFacetAt (B.translatedApartmentMap g p))
  rw [B.buildingFacetClosure_at_translatedApartmentMap hD]
  constructor
  · intro h
    exact ⟨q, h, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hinj : Function.Injective B.apartmentMap :=
      B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus
    have hzq := B.translatedApartmentMap_injective hinj g heq
    subst z
    exact hz

/-- The preimage of a lifted combinatorial closed facet is exactly the
original combinatorial closed facet. -/
theorem preimage_buildingFacetClosure_facetLift (Fc : BuildingFacet B) :
    e ⁻¹' C.buildingFacetClosure (facetLift B C e Fc) =
      B.buildingFacetClosure Fc := by
  obtain ⟨x, hx⟩ := Fc.property.nonempty
  rw [facetLift_of_mem B C φ e a hequiv hapt hfacet hD hcommon Fc hx]
  have hFc := (B.buildingFacetAt_eq_iff_mem hD x Fc).mpr hx
  ext y
  change e y ∈ C.buildingFacetClosure (C.buildingFacetAt (e x)) ↔ _
  rw [mem_buildingFacetClosure_image_iff B C φ e a hequiv hapt hfacet hD hcommon,
    hFc]

/-- The image of a closed facet is the intersection of its lifted full
closed facet with the image of the point map. -/
theorem image_buildingFacetClosure_facetLift (Fc : BuildingFacet B) :
    e '' B.buildingFacetClosure Fc =
      C.buildingFacetClosure (facetLift B C e Fc) ∩ Set.range e := by
  rw [← preimage_buildingFacetClosure_facetLift B C φ e a hequiv hapt hfacet
    hD hcommon Fc, Set.image_preimage_eq_inter_range]

/-- The full-facet lift preserves and reflects the original face relation. -/
theorem facetPrecedes_facetLift_iff (Fc Fd : BuildingFacet B) :
    C.FacetPrecedes (facetLift B C e Fc) (facetLift B C e Fd) ↔
      FacetPrecedes B Fc Fd := by
  obtain ⟨x, hx⟩ := Fc.property.nonempty
  obtain ⟨y, hy⟩ := Fd.property.nonempty
  rw [facetLift_of_mem B C φ e a hequiv hapt hfacet hD hcommon Fc hx,
    facetLift_of_mem B C φ e a hequiv hapt hfacet hD hcommon Fd hy,
    ← C.mem_buildingFacetClosure_iff_facetPrecedes,
    mem_buildingFacetClosure_image_iff B C φ e a hequiv hapt hfacet hD hcommon,
    B.mem_buildingFacetClosure_iff_facetPrecedes hD,
    (B.buildingFacetAt_eq_iff_mem hD x Fc).mpr hx,
    (B.buildingFacetAt_eq_iff_mem hD y Fd).mpr hy]

/-- The facet correspondence is an order isomorphism onto the full target
facets meeting the image, for the explicit original incidence orders. -/
def facetRangeOrderIso :
    @OrderIso (BuildingFacet B)
      {Fd : C.BuildingFacet // (Fd.val ∩ Set.range e).Nonempty}
      (B.buildingFacetPartialOrder hD
        (B.apartment.apartmentMap_injective B.isConnectedReductive
          B.isMaximalSplitTorus)).toLE
      ⟨fun Fd Fe => C.FacetPrecedes Fd.val Fe.val⟩ := by
  exact
    { facetRangeEquiv B C φ e a hequiv hapt hfacet hD hcommon with
      map_rel_iff' := by
        intro Fc Fd
        change C.FacetPrecedes
          ((facetRangeEquiv B C φ e a hequiv hapt hfacet hD hcommon Fc).val)
          ((facetRangeEquiv B C φ e a hequiv hapt hfacet hD hcommon Fd).val) ↔
            FacetPrecedes B Fc Fd
        rw [facetRangeEquiv_val, facetRangeEquiv_val]
        exact facetPrecedes_facetLift_iff B C φ e a hequiv hapt hfacet
          hD hcommon Fc Fd }

@[simp] theorem facetRangeOrderIso_val (Fc : BuildingFacet B) :
    (facetRangeOrderIso B C φ e a hequiv hapt hfacet hD hcommon Fc).val =
      facetLift B C e Fc := rfl

end Langlands.Geometry.Building.ValuationBuildingData
