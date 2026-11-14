import Langlands.Geometry.Building.ValuationBuildingQuotientComparison
import Langlands.Geometry.Building.IntegerBuildingFacetOrder

/-! # Facets along an apartment-compatible building embedding -/

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

theorem mem_buildingFacetAt_image_chart_iff (g : rationalPoints G)
    (x y : B.Apartment) :
    e (B.translatedApartmentMap g y) ∈
        (C.buildingFacetAt (e (B.translatedApartmentMap g x))).val ↔
      y ∈ AffineRootSystem.facet B.affineRoots x := by
  simp only [translatedApartmentMap, hequiv, hapt]
  change C.translatedApartmentMap (φ g) (a y) ∈
      (C.buildingFacetAt (C.translatedApartmentMap (φ g) (a x))).val ↔ _
  rw [C.buildingFacetAt_translatedApartmentMap]
  constructor
  · rintro ⟨z, hz, heq⟩
    have hzy := C.translatedApartmentMap_injective C.apartmentMap_injective (φ g) heq
    subst z
    exact (Set.ext_iff.mp (hfacet x) y).mp hz
  · intro hy
    exact ⟨a y, (Set.ext_iff.mp (hfacet x) y).mpr hy, rfl⟩

variable (hD : B.SatisfiesApartmentAxioms) (hcommon : B.HasCommonApartments)

include hD hcommon

/-- The ambient full facet through an image point cuts out exactly its
original full facet. Common apartments reduce the assertion to `hfacet`. -/
theorem mem_buildingFacetAt_image_iff (x y : B.ReducedBuilding) :
    e y ∈ (C.buildingFacetAt (e x)).val ↔ y ∈ (B.buildingFacetAt x).val := by
  obtain ⟨g, p, q, rfl, rfl⟩ := hcommon x y
  change e (B.translatedApartmentMap g q) ∈
      (C.buildingFacetAt (e (B.translatedApartmentMap g p))).val ↔ _
  rw [mem_buildingFacetAt_image_chart_iff B C φ e a hequiv hapt hfacet]
  change q ∈ AffineRootSystem.facet B.affineRoots p ↔
    B.translatedApartmentMap g q ∈
      (B.buildingFacetAt (B.translatedApartmentMap g p)).val
  rw [B.buildingFacetAt_translatedApartmentMap hD]
  constructor
  · intro h
    exact ⟨q, h, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hinj : Function.Injective B.apartmentMap :=
      B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus
    have hzq := B.translatedApartmentMap_injective hinj g heq
    subst z
    exact hz

omit hequiv hapt hfacet hD hcommon in
/-- Send a source facet to the unique ambient full facet containing the
image of one of its points. Independence of the chosen point is proved below. -/
def facetLift (Fc : BuildingFacet B) : C.BuildingFacet :=
  C.buildingFacetAt (e Fc.property.nonempty.choose)

/-- Pulling an ambient lifted facet back recovers the original facet. -/
theorem preimage_facetLift (Fc : BuildingFacet B) :
    e ⁻¹' (facetLift B C e Fc).val = Fc.val := by
  have hFc : B.buildingFacetAt Fc.property.nonempty.choose = Fc :=
    (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr Fc.property.nonempty.choose_spec
  ext y
  change e y ∈ (C.buildingFacetAt (e Fc.property.nonempty.choose)).val ↔ y ∈ Fc.val
  rw [mem_buildingFacetAt_image_iff B C φ e a hequiv hapt hfacet hD hcommon, hFc]

theorem facetLift_of_mem (Fc : BuildingFacet B) {x : B.ReducedBuilding}
    (hx : x ∈ Fc.val) :
    facetLift B C e Fc = C.buildingFacetAt (e x) := by
  symm
  apply (C.buildingFacetAt_eq_iff_mem _ _).mpr
  exact (Set.ext_iff.mp
    (preimage_facetLift B C φ e a hequiv hapt hfacet hD hcommon Fc) x).mpr hx

/-- The source facet image is the intersection of its lifted full facet
with the image of the point map. -/
theorem image_facetLift (Fc : BuildingFacet B) :
    e '' Fc.val = (facetLift B C e Fc).val ∩ Set.range e := by
  have hp := preimage_facetLift B C φ e a hequiv hapt hfacet hD hcommon Fc
  rw [← hp, Set.image_preimage_eq_inter_range]

theorem facetLift_injective : Function.Injective (facetLift B C e) := by
  intro Fc Fd h
  apply Subtype.ext
  rw [← preimage_facetLift B C φ e a hequiv hapt hfacet hD hcommon Fc,
    ← preimage_facetLift B C φ e a hequiv hapt hfacet hD hcommon Fd, h]

theorem facetLift_meets_range (Fc : BuildingFacet B) :
    ((facetLift B C e Fc).val ∩ Set.range e).Nonempty := by
  rw [← image_facetLift B C φ e a hequiv hapt hfacet hD hcommon Fc]
  exact Fc.property.nonempty.image e

/-- Exactly the full facets meeting the point-map image occur as lifts. -/
theorem facetLift_surjective_on_range (Fd : C.BuildingFacet)
    (hFd : (Fd.val ∩ Set.range e).Nonempty) :
    ∃ Fc : BuildingFacet B, facetLift B C e Fc = Fd := by
  obtain ⟨_, hy, x, rfl⟩ := hFd
  refine ⟨B.buildingFacetAt x, ?_⟩
  rw [facetLift_of_mem B C φ e a hequiv hapt hfacet hD hcommon _
    (B.mem_buildingFacetAt x)]
  exact (C.buildingFacetAt_eq_iff_mem _ Fd).mpr hy

/-- Facets of the source are precisely the ambient full facets meeting
the image of its point map. -/
def facetRangeEquiv :
    BuildingFacet B ≃ {Fd : C.BuildingFacet // (Fd.val ∩ Set.range e).Nonempty} :=
  Equiv.ofBijective
    (fun Fc => ⟨facetLift B C e Fc,
      facetLift_meets_range B C φ e a hequiv hapt hfacet hD hcommon Fc⟩)
    ⟨fun Fc Fd h => facetLift_injective B C φ e a hequiv hapt hfacet hD hcommon
        (congrArg Subtype.val h),
      fun Fd => by
        obtain ⟨Fc, hFc⟩ :=
          facetLift_surjective_on_range B C φ e a hequiv hapt hfacet hD hcommon
            Fd.val Fd.property
        exact ⟨Fc, Subtype.ext hFc⟩⟩

@[simp] theorem facetRangeEquiv_val (Fc : BuildingFacet B) :
    (facetRangeEquiv B C φ e a hequiv hapt hfacet hD hcommon Fc).val =
      facetLift B C e Fc := rfl

end Langlands.Geometry.Building.ValuationBuildingData
