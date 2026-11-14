import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Langlands.Geometry.Building.BuildingFacetPartition

/-! # Full facets under an equivariant restricted-apartment map -/

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

include hequiv hap in
theorem map_translatedApartmentMap (g : rationalPoints G) (x : B.Apartment) :
    e (B.translatedApartmentMap g x) = C.translatedApartmentMap (ρ g) (a x) := by
  change e (g • B.apartmentMap x) = ρ g • C.apartmentMap (a x)
  rw [hequiv, hap]

include hD hcommon hequiv hap hfac

/-- Membership in the same full facet is preserved and reflected by the map
of the original building quotients. -/
theorem map_mem_buildingFacetAt_iff (x y : B.ReducedBuilding) :
    e y ∈ (C.buildingFacetAt (e x)).val ↔
      y ∈ (B.buildingFacetAt x).val := by
  obtain ⟨Y, ⟨g, rfl⟩, hx, hy⟩ := hcommon x y
  obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hy
  change e (B.translatedApartmentMap g t) ∈
      (C.buildingFacetAt (e (B.translatedApartmentMap g s))).val ↔
    B.translatedApartmentMap g t ∈
      (B.buildingFacetAt (B.translatedApartmentMap g s)).val
  rw [B.map_translatedApartmentMap C ρ e a hequiv hap,
    B.map_translatedApartmentMap C ρ e a hequiv hap,
    C.buildingFacetAt_translatedApartmentMap,
    B.buildingFacetAt_translatedApartmentMap hD]
  rw [Set.mem_image, Set.mem_image]
  constructor
  · rintro ⟨z, hz, heq⟩
    have hza : z = a t :=
      C.translatedApartmentMap_injective C.apartmentMap_injective (ρ g) heq
    have ht : t ∈ AffineRootSystem.facet B.affineRoots s := by
      rw [← hfac s]
      change a t ∈ AffineRootSystem.facet C.affineRoots (a s)
      exact hza ▸ hz
    exact ⟨t, ht, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hmaps := congrArg e heq
    rw [B.map_translatedApartmentMap C ρ e a hequiv hap,
      B.map_translatedApartmentMap C ρ e a hequiv hap] at hmaps
    have hza : a z = a t :=
      C.translatedApartmentMap_injective C.apartmentMap_injective (ρ g) hmaps
    have haz : a z ∈ AffineRootSystem.facet C.affineRoots (a s) := by
      have : z ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a s) := by
        rwa [hfac s]
      exact this
    exact ⟨a t, hza ▸ haz, rfl⟩

/-- The map of quotient points reflects and preserves their containing facets. -/
theorem mapped_buildingFacetAt_eq_iff (x y : B.ReducedBuilding) :
    C.buildingFacetAt (e x) = C.buildingFacetAt (e y) ↔
      B.buildingFacetAt x = B.buildingFacetAt y := by
  rw [eq_comm, C.buildingFacetAt_eq_iff_mem,
    B.map_mem_buildingFacetAt_iff C ρ e a hD hcommon hequiv hap hfac,
    eq_comm, B.buildingFacetAt_eq_iff_mem hD]

/-- Map each full downstairs facet to its containing full upstairs facet.
The exact restricted-facet identity makes this an embedding. -/
def facetRestrictionEmbedding : BuildingFacet B ↪ C.BuildingFacet where
  toFun Fc := C.buildingFacetAt (e Fc.property.nonempty.choose)
  inj' := by
    intro Fc Fd heq
    have hFc := (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr
      Fc.property.nonempty.choose_spec
    have hFd := (B.buildingFacetAt_eq_iff_mem hD _ Fd).mpr
      Fd.property.nonempty.choose_spec
    have hxy := (B.mapped_buildingFacetAt_eq_iff C ρ e a
      hD hcommon hequiv hap hfac _ _).mp heq
    exact hFc.symm.trans (hxy.trans hFd)

/-- Pulling back the containing upstairs facet recovers the entire downstairs
facet, including points outside its chosen presentation. -/
theorem preimage_facetRestrictionEmbedding (Fc : BuildingFacet B) :
    e ⁻¹' (B.facetRestrictionEmbedding C ρ e a
      hD hcommon hequiv hap hfac Fc).val = Fc.val := by
  ext y
  change e y ∈ (C.buildingFacetAt (e Fc.property.nonempty.choose)).val ↔ y ∈ Fc.val
  rw [B.map_mem_buildingFacetAt_iff C ρ e a hD hcommon hequiv hap hfac,
    (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr Fc.property.nonempty.choose_spec]

theorem image_subset_facetRestrictionEmbedding (Fc : BuildingFacet B) :
    e '' Fc.val ⊆ (B.facetRestrictionEmbedding C ρ e a
      hD hcommon hequiv hap hfac Fc).val := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ e ⁻¹' (B.facetRestrictionEmbedding C ρ e a
      hD hcommon hequiv hap hfac Fc).val := by
    rwa [B.preimage_facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac]
  exact hx'

@[simp] theorem facetRestrictionEmbedding_buildingFacetAt (x : B.ReducedBuilding) :
    B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac
      (B.buildingFacetAt x) = C.buildingFacetAt (e x) := by
  symm
  apply (C.buildingFacetAt_eq_iff_mem _ _).mpr
  exact B.image_subset_facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac
    _ ⟨x, B.mem_buildingFacetAt x, rfl⟩

end Langlands.Geometry.Building.ValuationBuildingData
