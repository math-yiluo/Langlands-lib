import Langlands.Geometry.Building.FullValidity.Realization
import Langlands.Geometry.Building.ApartmentFixedPointReduction

/-! # Common apartments from the polysimplicial building axiom -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Every point of the existing quotient lies in one of its existing facets. -/
theorem exists_buildingFacet_mem (x : B.ReducedBuilding) :
    ∃ Fc : BuildingFacet B, x ∈ (Fc : Set B.ReducedBuilding) := by
  obtain ⟨g, a, rfl⟩ := B.exists_smul_apartmentMap x
  refine ⟨⟨(fun z => g • B.apartmentMap z) ''
    AffineRootSystem.facet B.affineRoots a,
    ⟨g, AffineRootSystem.facet B.affineRoots a,
      AffineRootSystem.isFacet_facet _ _, rfl⟩⟩, ?_⟩
  exact ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩

namespace PolysimplicialRealization

variable {B} (R : B.PolysimplicialRealization)

/-- The abstract building axiom for the supplied realization gives an actual
translated apartment containing any two points of the original quotient. -/
theorem exists_isApartment_mem_mem
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) :
    ∃ Y : Set B.ReducedBuilding, B.IsApartment Y ∧ x ∈ Y ∧ y ∈ Y := by
  obtain ⟨Fx, hx⟩ := B.exists_buildingFacet_mem x
  obtain ⟨Fy, hy⟩ := B.exists_buildingFacet_mem y
  let fx : R.complex.facets := R.realize.symm Fx
  let fy : R.complex.facets := R.realize.symm Fy
  obtain ⟨C, hC, hfxC⟩ := hR.isChamberComplex.2.1 _ fx.property
  obtain ⟨D, hD, hfyD⟩ := hR.isChamberComplex.2.1 _ fy.property
  obtain ⟨𝒜, h𝒜, hC𝒜, hD𝒜⟩ := hR.exists_apartment C D hC hD
  have hfx𝒜 := (hR.isSubcomplex 𝒜 h𝒜).2 C hC𝒜 _ fx.property hfxC
  have hfy𝒜 := (hR.isSubcomplex 𝒜 h𝒜).2 D hD𝒜 _ fy.property hfyD
  obtain ⟨Y, hY, h𝒜Y⟩ := h𝒜
  rw [h𝒜Y] at hfx𝒜 hfy𝒜
  obtain ⟨_, hFxY⟩ := hfx𝒜
  obtain ⟨_, hFyY⟩ := hfy𝒜
  change (R.realize fx).val ⊆ Y at hFxY
  change (R.realize fy).val ⊆ Y at hFyY
  have hxY : (Fx : Set B.ReducedBuilding) ⊆ Y := by simpa [fx] using hFxY
  have hyY : (Fy : Set B.ReducedBuilding) ⊆ Y := by simpa [fy] using hFyY
  exact ⟨Y, hY, hxY hx, hyY hy⟩

/-- Choose a genuine common translated apartment in the existing quotient,
using the building axiom of the supplied polysimplicial realization. -/
def commonApartment
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) : Set B.ReducedBuilding :=
  (R.exists_isApartment_mem_mem hR x y).choose

theorem commonApartment_spec
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) :
    B.IsApartment (R.commonApartment hR x y) ∧
      x ∈ R.commonApartment hR x y ∧ y ∈ R.commonApartment hR x y :=
  (R.exists_isApartment_mem_mem hR x y).choose_spec

/-- Every point shares an apartment with every other point under the supplied
realization's building axiom. -/
theorem hasCommonApartmentWith_of_isBuilding
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x : B.ReducedBuilding) : B.HasCommonApartmentWith x :=
  fun y => R.exists_isApartment_mem_mem hR x y

/-- A singleton apartment fixed locus for the existing norm-one stabilizer
extends globally under the supplied realization's building axiom. -/
theorem eq_of_compactStabilizer_fixed_of_isBuilding
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (hB : B.apartment.IsTopologyCompatible) (x : B.Apartment)
    (hlocal : B.HasApartmentFixedPointUniqueness
      (B.compactStabilizer (B.apartmentMap x)) (B.apartmentMap x))
    (y : B.ReducedBuilding)
    (hy : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer (B.apartmentMap x) → g • y = y) :
    y = B.apartmentMap x :=
  B.eq_of_compactStabilizer_fixed_of_apartment hB x
    (R.hasCommonApartmentWith_of_isBuilding hR _) hlocal y hy

end PolysimplicialRealization

end Langlands.Geometry.Building.ValuationBuildingData
