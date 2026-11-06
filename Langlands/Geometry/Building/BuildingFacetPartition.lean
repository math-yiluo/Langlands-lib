import Langlands.Geometry.Building.ApartmentFacetConstruction
import Langlands.Geometry.Building.CommonApartmentConstruction
import Mathlib.Data.Setoid.Basic

/-! # The partition of the actual valuation quotient by building facets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A : Type u} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Two affine facets containing a common point coincide. -/
theorem IsFacet.eq_of_mem_mem {Fa Fb : Set A} (hFa : IsFacet Ψ Fa)
    (hFb : IsFacet Ψ Fb) {x : A} (ha : x ∈ Fa) (hb : x ∈ Fb) : Fa = Fb := by
  obtain ⟨a, rfl⟩ := hFa
  obtain ⟨b, rfl⟩ := hFb
  exact (facet_eq_of_mem ha).symm.trans (facet_eq_of_mem hb)

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- A point shared by two facets of the original quotient determines the
whole facet. This uses no opposite-factor-pair hypothesis. -/
theorem IsFacet.eq_of_mem_mem
    (hD : B.SatisfiesApartmentAxioms)
    {Y Z : Set B.ReducedBuilding} (hY : B.IsFacet Y) (hZ : B.IsFacet Z)
    {x : B.ReducedBuilding} (hxY : x ∈ Y) (hxZ : x ∈ Z) : Y = Z := by
  obtain ⟨g, Fa, hFa, rfl⟩ := hY
  obtain ⟨h, Fb, hFb, rfl⟩ := hZ
  obtain ⟨a, ha, rfl⟩ := hxY
  obtain ⟨b, hb, hab⟩ := hxZ
  change h • B.apartmentMap b = g • B.apartmentMap a at hab
  have hab' : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    rw [mul_smul, ← hab, inv_smul_smul]
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_eq_on_translated_facet hD hFa ha (h⁻¹ * g) hab'
  have hnFa : n • Fa = Fb :=
    (B.normalizer_smul_isFacet hD hFa n).eq_of_mem_mem hFb
      (hn ▸ Set.smul_mem_smul_set ha) hb
  calc
    (fun y => g • B.apartmentMap y) '' Fa =
        (fun y => h • B.apartmentMap (n • y)) '' Fa := by
      apply Set.image_congr
      intro y hy
      have H := congrArg (h • ·) (heq y hy)
      simpa only [mul_smul, smul_inv_smul] using H
    _ = (fun y => h • B.apartmentMap y) '' (n • Fa) := by
      change _ = (fun y => h • B.apartmentMap y) '' ((fun y => n • y) '' Fa)
      rw [Set.image_image]
    _ = _ := by rw [hnFa]

/-- Distinct building facets are disjoint. -/
theorem IsFacet.disjoint_of_ne
    (hD : B.SatisfiesApartmentAxioms)
    {Y Z : Set B.ReducedBuilding} (hY : B.IsFacet Y) (hZ : B.IsFacet Z)
    (hne : Y ≠ Z) : Disjoint Y Z := by
  rw [Set.disjoint_left]
  intro x hxY hxZ
  exact hne (hY.eq_of_mem_mem B hD hZ hxY hxZ)

/-- Every point lies in exactly one of the original building facets. -/
theorem existsUnique_buildingFacet_mem
    (hD : B.SatisfiesApartmentAxioms) (x : B.ReducedBuilding) :
    ∃! Fc : BuildingFacet B, x ∈ (Fc : Set B.ReducedBuilding) := by
  obtain ⟨Fc, hx⟩ := B.exists_buildingFacet_mem x
  refine ⟨Fc, hx, fun Fd hd => ?_⟩
  exact Subtype.ext (Fd.property.eq_of_mem_mem B hD Fc.property hd hx)

/-- Choose the building facet through a quotient point. The containing-facet
property is unconditional; uniqueness is proved under the apartment axioms. -/
def buildingFacetAt (x : B.ReducedBuilding) : BuildingFacet B :=
  (B.exists_buildingFacet_mem x).choose

theorem mem_buildingFacetAt (x : B.ReducedBuilding) :
    x ∈ (B.buildingFacetAt x : Set B.ReducedBuilding) :=
  (B.exists_buildingFacet_mem x).choose_spec

/-- The chosen facet is characterized by containment of the given point. -/
theorem buildingFacetAt_eq_iff_mem
    (hD : B.SatisfiesApartmentAxioms) (x : B.ReducedBuilding) (Fc : BuildingFacet B) :
    B.buildingFacetAt x = Fc ↔ x ∈ (Fc : Set B.ReducedBuilding) := by
  constructor
  · intro h
    rw [← h]
    exact B.mem_buildingFacetAt x
  · intro h
    exact Subtype.ext ((B.buildingFacetAt x).property.eq_of_mem_mem B hD Fc.property
      (B.mem_buildingFacetAt x) h)

/-- On any apartment chart the chosen facet is exactly the translated image
of the affine facet through the given coordinates. -/
theorem buildingFacetAt_translatedApartmentMap
    (hD : B.SatisfiesApartmentAxioms) (g : rationalPoints G) (a : B.Apartment) :
    (B.buildingFacetAt (B.translatedApartmentMap g a) : Set B.ReducedBuilding) =
      B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a := by
  apply (B.buildingFacetAt _).property.eq_of_mem_mem B hD
    (show B.IsFacet (B.translatedApartmentMap g ''
      AffineRootSystem.facet B.affineRoots a) from
        ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩)
    (B.mem_buildingFacetAt _)
  exact ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩

/-- The chosen facet construction respects the original rational-point action. -/
theorem buildingFacetAt_smul
    (hD : B.SatisfiesApartmentAxioms) (g : rationalPoints G) (x : B.ReducedBuilding) :
    (B.buildingFacetAt (g • x) : Set B.ReducedBuilding) =
      g • (B.buildingFacetAt x : Set B.ReducedBuilding) :=
  (B.buildingFacetAt _).property.eq_of_mem_mem B hD
    ((B.buildingFacetAt x).property.smul B g) (B.mem_buildingFacetAt _)
    (Set.smul_mem_smul_set (B.mem_buildingFacetAt x))

/-- Equality of containing facets is precisely membership in the same facet. -/
theorem buildingFacetAt_eq_buildingFacetAt_iff
    (hD : B.SatisfiesApartmentAxioms) (x y : B.ReducedBuilding) :
    B.buildingFacetAt x = B.buildingFacetAt y ↔
      y ∈ (B.buildingFacetAt x : Set B.ReducedBuilding) := by
  rw [eq_comm, B.buildingFacetAt_eq_iff_mem hD]

/-- Every original building facet is attained by the containing-facet map. -/
theorem buildingFacetAt_surjective (hD : B.SatisfiesApartmentAxioms) :
    Function.Surjective B.buildingFacetAt := by
  intro Fc
  obtain ⟨x, hx⟩ := Fc.property.nonempty
  exact ⟨x, (B.buildingFacetAt_eq_iff_mem hD x Fc).mpr hx⟩

/-- The equivalence relation of lying in the same original building facet. -/
def buildingFacetSetoid : Setoid B.ReducedBuilding :=
  Setoid.ker B.buildingFacetAt

/-- The quotient of the original point carrier by its facet partition is
exactly the existing type of building facets. -/
def buildingFacetQuotientEquiv (hD : B.SatisfiesApartmentAxioms) :
    Quotient B.buildingFacetSetoid ≃ BuildingFacet B :=
  Setoid.quotientKerEquivOfSurjective B.buildingFacetAt (B.buildingFacetAt_surjective hD)

end ValuationBuildingData
end Langlands.Geometry.Building
