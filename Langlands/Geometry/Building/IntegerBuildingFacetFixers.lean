import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-! # Pointwise fixers of integer-building facets and their closures -/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {p x : A}

/-- A formal closed-facet point has its midpoint with the base point in the
original open sign facet. No root-system hypothesis is required. -/
theorem midpoint_mem_facet_of_mem_facetClosure (hx : x ∈ facetClosure Ψ p) :
    midpoint ℝ p x ∈ facet Ψ p := by
  intro ψ hψ
  have heval : ψ (midpoint ℝ p x) = (ψ p + ψ x) / 2 := by
    rw [AffineMap.map_midpoint, midpoint_eq_smul_add]
    simp [invOf_eq_inv, div_eq_mul_inv, mul_comm]
  rcases lt_trichotomy (ψ p) 0 with hneg | hzero | hpos
  · have hxle : ψ x ≤ 0 := by
      rcases hx ψ hψ with h | h
      · exact le_of_eq (sign_eq_zero_iff.mp h)
      · exact le_of_lt (sign_eq_neg_one_iff.mp (h.trans (sign_neg hneg)))
    rw [sign_neg hneg, sign_neg (show ψ (midpoint ℝ p x) < 0 by
      rw [heval]; linarith)]
  · have hxzero : ψ x = 0 := by
      rcases hx ψ hψ with h | h
      · exact sign_eq_zero_iff.mp h
      · exact sign_eq_zero_iff.mp (by simpa [hzero] using h)
    simp [heval, hzero, hxzero]
  · have hxge : 0 ≤ ψ x := by
      rcases hx ψ hψ with h | h
      · exact le_of_eq (sign_eq_zero_iff.mp h).symm
      · exact le_of_lt (sign_eq_one_iff.mp (h.trans (sign_pos hpos)))
    rw [sign_pos hpos, sign_pos (show 0 < ψ (midpoint ℝ p x) by
      rw [heval]; linarith)]

/-- Any affine map fixing an open sign facet fixes its formal closure. -/
theorem affineMap_eq_self_of_facet_fixed (e : A →ᵃ[ℝ] A)
    (hfix : ∀ y ∈ facet Ψ p, e y = y) (hx : x ∈ facetClosure Ψ p) :
    e x = x := by
  have hp := hfix p (mem_facet_self Ψ p)
  have hm := hfix (midpoint ℝ p x) (midpoint_mem_facet_of_mem_facetClosure hx)
  rw [AffineMap.map_midpoint, hp] at hm
  simpa using ((midpoint_eq_iff).mp hm).symm

end AffineRootSystem

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- Fixation of every point of an apartment facet in the actual quotient
extends to the whole formal closed facet. -/
theorem smul_apartmentMap_eq_of_facet_fixed
    {h : rationalPoints G} {p x : B.Apartment}
    (hfix : ∀ y ∈ AffineRootSystem.facet B.affineRoots p,
      h • B.apartmentMap y = B.apartmentMap y)
    (hx : x ∈ AffineRootSystem.facetClosure B.affineRoots p) :
    h • B.apartmentMap x = B.apartmentMap x := by
  obtain ⟨n, _, heq⟩ := B.exists_normalizer_eq_on_translated_facetClosure h
    (hfix p (AffineRootSystem.mem_facet_self _ _))
  have hnfix : ∀ y ∈ AffineRootSystem.facet B.affineRoots p,
      (B.apartment.normalizerAffineEquiv n).toAffineMap y = y := by
    intro y hy
    apply B.apartmentMap_injective
    exact (heq y (AffineRootSystem.facet_subset_facetClosure _ _ hy)).symm.trans
      (hfix y hy)
  have hnx := AffineRootSystem.affineMap_eq_self_of_facet_fixed
    (B.apartment.normalizerAffineEquiv n).toAffineMap hnfix hx
  exact (heq x hx).trans (congrArg B.apartmentMap hnx)

/-- The original full facet and its combinatorial closure have identical
pointwise fixers in the original rational-point group. -/
theorem pointwiseFixer_buildingFacetClosure (C : B.BuildingFacet) :
    B.pointwiseFixer (B.buildingFacetClosure C) = B.pointwiseFixer C.val := by
  apply le_antisymm
  · intro h hh
    apply B.apartment.mem_pointwiseFixer.mpr
    intro y hy
    exact B.apartment.mem_pointwiseFixer.mp hh y
      (B.subset_buildingFacetClosure C hy)
  · intro h hh
    obtain ⟨g, _, ⟨p, rfl⟩, hC⟩ := C.property
    change C.val = B.translatedApartmentMap g '' _ at hC
    apply B.apartment.mem_pointwiseFixer.mpr
    rw [B.buildingFacetClosure_eq_image C g p hC]
    rintro _ ⟨x, hx, rfl⟩
    have hfix : ∀ y ∈ AffineRootSystem.facet B.affineRoots p,
        (g⁻¹ * h * g) • B.apartmentMap y = B.apartmentMap y := by
      intro y hy
      have hyC : B.translatedApartmentMap g y ∈ C.val := by
        rw [hC]
        exact ⟨y, hy, rfl⟩
      have hpoint := B.apartment.mem_pointwiseFixer.mp hh _ hyC
      change h • (g • B.apartmentMap y) = g • B.apartmentMap y at hpoint
      rw [mul_smul, mul_smul, hpoint, inv_smul_smul]
    have H := congrArg (g • ·) (B.smul_apartmentMap_eq_of_facet_fixed hfix hx)
    simpa only [translatedApartmentMap, mul_smul, smul_inv_smul] using H

/-- Pointwise fixers reverse the actual common-apartment facet incidence. -/
theorem pointwiseFixer_le_of_facetPrecedes
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C) :
    B.pointwiseFixer C.val ≤ B.pointwiseFixer F.val := by
  intro h hh
  have hh' : h ∈ B.pointwiseFixer (B.buildingFacetClosure C) := by
    rwa [B.pointwiseFixer_buildingFacetClosure C]
  apply B.apartment.mem_pointwiseFixer.mpr
  intro y hy
  exact B.apartment.mem_pointwiseFixer.mp hh' y
    ((B.facetPrecedes_iff_subset_buildingFacetClosure F C).mp hFC hy)

end IntegerValuationBuildingData

/-- The original integer-building full facets have the same pointwise fixers
as their combinatorial closures, and their incidence reverses fixer inclusion. -/
def IntegerBuildingFacetFixersStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (B : IntegerValuationBuildingData v G),
    (∀ C : B.BuildingFacet,
      B.pointwiseFixer (B.buildingFacetClosure C) = B.pointwiseFixer C.val) ∧
    ∀ F C : B.BuildingFacet, B.FacetPrecedes F C →
      B.pointwiseFixer C.val ≤ B.pointwiseFixer F.val

theorem integerBuildingFacetFixers : IntegerBuildingFacetFixersStatement.{u} := by
  intro k _ G _ v B
  exact ⟨B.pointwiseFixer_buildingFacetClosure, fun _ _ =>
    B.pointwiseFixer_le_of_facetPrecedes⟩

end Langlands.Geometry.Building
