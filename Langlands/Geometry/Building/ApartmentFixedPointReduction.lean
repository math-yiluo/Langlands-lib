import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.KPParahoricFixerComparison

/-! # From an apartment fixed locus to a global fixed point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Every point of the existing quotient shares an apartment with `x`. -/
def HasCommonApartmentWith (x : B.ReducedBuilding) : Prop :=
  ∀ z : B.ReducedBuilding,
    ∃ Y : Set B.ReducedBuilding, B.IsApartment Y ∧ x ∈ Y ∧ z ∈ Y

/-- Every `K`-fixed point lying in the base apartment equals `x`.
This predicate does not assert that `x` itself is fixed. -/
def HasApartmentFixedPointUniqueness
    (K : Subgroup (rationalPoints G)) (x : B.ReducedBuilding) : Prop :=
  ∀ z : B.ReducedBuilding, z ∈ B.apartmentImage →
    (∀ g : rationalPoints G, g ∈ K → g • z = z) → z = x

/-- If every point shares an apartment with `x`, and `K` moves those apartments
to the base apartment, every `K`-fixed point lies in the base apartment. -/
theorem mem_apartmentImage_of_fixed
    (K : Subgroup (rationalPoints G)) (x y : B.ReducedBuilding)
    (hcommon : B.HasCommonApartmentWith x)
    (htrans : ∀ Y : Set B.ReducedBuilding,
      B.IsApartment Y → x ∈ Y →
        ∃ g : rationalPoints G, g ∈ K ∧ g • Y = B.apartmentImage)
    (hy : ∀ g : rationalPoints G, g ∈ K → g • y = y) :
    y ∈ B.apartmentImage := by
  obtain ⟨Y, hY, hxY, hyY⟩ := hcommon y
  obtain ⟨g, hg, hgY⟩ := htrans Y hY hxY
  have : g • y ∈ g • Y := Set.smul_mem_smul_set hyY
  rwa [hy g hg, hgY] at this

/-- The singleton fixed-locus calculation in the base apartment gives global
uniqueness once common apartments and the stated subgroup transitivity are known. -/
theorem eq_of_fixed_of_apartment
    (K : Subgroup (rationalPoints G)) (x y : B.ReducedBuilding)
    (hcommon : B.HasCommonApartmentWith x)
    (htrans : ∀ Y : Set B.ReducedBuilding,
      B.IsApartment Y → x ∈ Y →
        ∃ g : rationalPoints G, g ∈ K ∧ g • Y = B.apartmentImage)
    (hlocal : B.HasApartmentFixedPointUniqueness K x)
    (hy : ∀ g : rationalPoints G, g ∈ K → g • y = y) :
    y = x :=
  hlocal y (B.mem_apartmentImage_of_fixed K x y hcommon htrans hy) hy

/-- The actual sharp fixer moves every apartment containing the displayed
apartment point to the base apartment. This follows from the quotient relation. -/
theorem exists_sharpFixer_smul_apartmentImage (x : B.Apartment)
    {Y : Set B.ReducedBuilding} (hY : B.IsApartment Y)
    (hx : B.apartmentMap x ∈ Y) :
    ∃ g : rationalPoints G, g ∈ B.sharpFixer {x} ∧
      g • Y = B.apartmentImage := by
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hx
  have heq :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, x) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, z) := by
    have hz' := hz.symm
    change ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, x) =
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, z) at hz'
    simpa only [mul_one] using hz'
  obtain ⟨n, _, hn⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily 1 g x z).mp heq
  have hp : g * (n : rationalPoints G) ∈ B.sharpFixer {x} := by
    change 1⁻¹ * g * (n : rationalPoints G) ∈ B.sharpFixer {x} at hn
    simpa only [inv_one, one_mul] using hn
  refine ⟨(g * (n : rationalPoints G))⁻¹, inv_mem hp, ?_⟩
  calc
    (g * (n : rationalPoints G))⁻¹ • (g • B.apartmentImage) =
        (n : rationalPoints G)⁻¹ • B.apartmentImage := by
      simp only [mul_inv_rev, mul_smul, inv_smul_smul]
    _ = B.apartmentImage :=
      B.normalizerPoints_le_stabilizer_apartmentImage (inv_mem n.property)

/-- A subgroup containing the actual sharp fixer needs no extra apartment
transitivity premise in the global uniqueness deduction. -/
theorem eq_of_fixed_of_sharpFixer_le
    (K : Subgroup (rationalPoints G)) (x : B.Apartment)
    (hsharp : B.sharpFixer {x} ≤ K)
    (hcommon : B.HasCommonApartmentWith (B.apartmentMap x))
    (hlocal : B.HasApartmentFixedPointUniqueness K (B.apartmentMap x))
    (y : B.ReducedBuilding)
    (hy : ∀ g : rationalPoints G, g ∈ K → g • y = y) :
    y = B.apartmentMap x := by
  apply B.eq_of_fixed_of_apartment K (B.apartmentMap x) y hcommon _ hlocal hy
  intro Y hY hx
  obtain ⟨g, hg, hgY⟩ := B.exists_sharpFixer_smul_apartmentImage x hY hx
  exact ⟨g, hsharp hg, hgY⟩

/-- For topology-compatible valuation data, a singleton apartment fixed locus
for the actual norm-one stabilizer extends to the entire quotient whenever
each point shares an apartment with the base point. -/
theorem eq_of_compactStabilizer_fixed_of_apartment
    (hB : B.apartment.IsTopologyCompatible) (x : B.Apartment)
    (hcommon : B.HasCommonApartmentWith (B.apartmentMap x))
    (hlocal : B.HasApartmentFixedPointUniqueness
      (B.compactStabilizer (B.apartmentMap x)) (B.apartmentMap x))
    (y : B.ReducedBuilding)
    (hy : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer (B.apartmentMap x) → g • y = y) :
    y = B.apartmentMap x :=
  B.eq_of_fixed_of_sharpFixer_le (B.compactStabilizer (B.apartmentMap x)) x
    (B.sharpFixer_le_compactStabilizer hB (Set.mem_singleton x)) hcommon hlocal y hy

end Langlands.Geometry.Building.ValuationBuildingData
