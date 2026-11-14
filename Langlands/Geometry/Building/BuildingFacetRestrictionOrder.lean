import Langlands.Geometry.Building.BuildingFacetRestrictionEmbedding
import Langlands.Geometry.Building.BuildingFacetClosure
import Langlands.Geometry.Building.AffineFacetRestrictionClosure

/-! # Incidence and closed facets under exact facet restriction -/

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
  {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (C : IntegerValuationBuildingData v H)
  (ρ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

include hD hcommon hequiv hap hfac

/-- Membership in the full combinatorial closed facet through a point is
preserved and reflected by the original quotient point map. -/
theorem map_mem_buildingFacetClosure_at_iff (x y : B.ReducedBuilding) :
    e y ∈ C.buildingFacetClosure (C.buildingFacetAt (e x)) ↔
      y ∈ B.buildingFacetClosure (B.buildingFacetAt x) := by
  obtain ⟨Y, ⟨g, rfl⟩, hx, hy⟩ := hcommon x y
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hy
  change e (B.translatedApartmentMap g t) ∈
      C.buildingFacetClosure (C.buildingFacetAt (e (B.translatedApartmentMap g s))) ↔
    B.translatedApartmentMap g t ∈
      B.buildingFacetClosure (B.buildingFacetAt (B.translatedApartmentMap g s))
  rw [B.map_translatedApartmentMap C ρ e a hequiv hap,
    B.map_translatedApartmentMap C ρ e a hequiv hap,
    C.buildingFacetClosure_at_translatedApartmentMap,
    B.buildingFacetClosure_at_translatedApartmentMap hD]
  have hcl := AffineRootSystem.preimage_facetClosure_eq_of_preimage_facet_eq
    a B.affineRoots C.affineRoots s (hfac s)
  rw [Set.mem_image, Set.mem_image]
  constructor
  · rintro ⟨z, hz, heq⟩
    have hza : z = a t :=
      C.translatedApartmentMap_injective C.apartmentMap_injective (ρ g) heq
    have ht : t ∈ AffineRootSystem.facetClosure B.affineRoots s := by
      rw [← hcl]
      change a t ∈ AffineRootSystem.facetClosure C.affineRoots (a s)
      exact hza ▸ hz
    exact ⟨t, ht, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hmaps := congrArg e heq
    rw [B.map_translatedApartmentMap C ρ e a hequiv hap,
      B.map_translatedApartmentMap C ρ e a hequiv hap] at hmaps
    have hza : a z = a t :=
      C.translatedApartmentMap_injective C.apartmentMap_injective (ρ g) hmaps
    have haz : a z ∈ AffineRootSystem.facetClosure C.affineRoots (a s) := by
      have : z ∈ a ⁻¹' AffineRootSystem.facetClosure C.affineRoots (a s) := by
        rwa [hcl]
      exact this
    exact ⟨a t, hza ▸ haz, rfl⟩

/-- The entire inverse image of the assigned upstairs closed facet is the
original downstairs closed facet. -/
theorem preimage_buildingFacetClosure_facetRestrictionEmbedding (Fc : BuildingFacet B) :
    e ⁻¹' C.buildingFacetClosure (B.facetRestrictionEmbedding C ρ e a
      hD hcommon hequiv hap hfac Fc) = B.buildingFacetClosure Fc := by
  ext y
  change e y ∈ C.buildingFacetClosure
      (C.buildingFacetAt (e Fc.property.nonempty.choose)) ↔
    y ∈ B.buildingFacetClosure Fc
  rw [B.map_mem_buildingFacetClosure_at_iff C ρ e a hD hcommon hequiv hap hfac,
    (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr Fc.property.nonempty.choose_spec]

/-- Exact affine-facet restriction preserves and reflects full building
incidence, including equality. -/
theorem facetRestrictionEmbedding_facetPrecedes_iff (Fc Fd : BuildingFacet B) :
    C.FacetPrecedes
      (B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fc)
      (B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fd) ↔
      FacetPrecedes B Fc Fd := by
  obtain ⟨x, hx⟩ := Fc.property.nonempty
  have hxup := B.image_subset_facetRestrictionEmbedding C ρ e a
    hD hcommon hequiv hap hfac Fc ⟨x, hx, rfl⟩
  have hxcl : e x ∈ C.buildingFacetClosure
      (B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fd) ↔
      x ∈ B.buildingFacetClosure Fd := by
    change x ∈ e ⁻¹' C.buildingFacetClosure _ ↔ _
    rw [B.preimage_buildingFacetClosure_facetRestrictionEmbedding C ρ e a
      hD hcommon hequiv hap hfac]
  constructor
  · intro h
    apply (B.facetPrecedes_iff_nonempty_inter_buildingFacetClosure hD Fc Fd).mpr
    exact ⟨x, hx, hxcl.mp
      ((C.facetPrecedes_iff_subset_buildingFacetClosure _ _).mp h hxup)⟩
  · intro h
    apply (C.facetPrecedes_iff_nonempty_inter_buildingFacetClosure _ _).mpr
    exact ⟨e x, hxup, hxcl.mpr
      ((B.facetPrecedes_iff_subset_buildingFacetClosure hD Fc Fd).mp h hx)⟩

/-- With the existing explicit incidence orders, the same full-facet
restriction map is an order embedding. -/
def facetRestrictionOrderEmbedding (hinj : Function.Injective B.apartmentMap) :
    @OrderEmbedding (BuildingFacet B) C.BuildingFacet
      (B.buildingFacetPartialOrder hD hinj).toLE C.buildingFacetPartialOrder.toLE where
  toEmbedding := B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac
  map_rel_iff' := B.facetRestrictionEmbedding_facetPrecedes_iff
    C ρ e a hD hcommon hequiv hap hfac _ _

@[simp] theorem facetRestrictionOrderEmbedding_apply
    (hinj : Function.Injective B.apartmentMap) (Fc : BuildingFacet B) :
    B.facetRestrictionOrderEmbedding C ρ e a hD hcommon hequiv hap hfac hinj Fc =
      B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fc :=
  rfl

end Langlands.Geometry.Building.ValuationBuildingData
