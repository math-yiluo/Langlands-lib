import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.AffineFacetTransport

/-!
# Transport of building axioms on the existing valuation quotients

The field, group, actual rational points and their topology remain fixed.
All comparison data and source witnesses are supplied explicitly.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B₁ B₂ : ValuationBuildingData G)
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)

/-- The image operation of a building isomorphism restricts to an equivalence
of the existing types of building facets. -/
def IsBuildingIso.facetEquiv (hiso : IsBuildingIso B₁ B₂ Φ) :
    BuildingFacet B₁ ≃ BuildingFacet B₂ :=
  Φ.setCongr.subtypeEquiv fun Y => (hiso.isFacet_image_iff Y).symm

@[simp] theorem IsBuildingIso.facetEquiv_apply (hiso : IsBuildingIso B₁ B₂ Φ)
    (Fc : BuildingFacet B₁) :
    (hiso.facetEquiv B₁ B₂ Φ Fc).val = Φ '' Fc.val := rfl

@[simp] theorem IsBuildingIso.facetEquiv_symm_apply (hiso : IsBuildingIso B₁ B₂ Φ)
    (Fc : BuildingFacet B₂) :
    ((hiso.facetEquiv B₁ B₂ Φ).symm Fc).val = Φ.symm '' Fc.val := rfl

section Equivariant

variable (hΦ : ∀ (g : rationalPoints G) (q : B₁.ReducedBuilding), Φ (g • q) = g • Φ q)

include hΦ

/-- An equivariant equivalence for the identity on actual rational points
identifies their point fixers as subgroups of the same group. -/
theorem fixer_eq_of_equivariantEquiv (q : B₁.ReducedBuilding) :
    B₂.fixer (Φ q) = B₁.fixer q := by
  ext g
  rw [B₂.mem_fixer, B₁.mem_fixer, ← hΦ]
  exact Φ.injective.eq_iff

/-- Intersecting with the same actual rational norm kernel identifies the
compact stabilizers. -/
theorem compactStabilizer_eq_of_equivariantEquiv (q : B₁.ReducedBuilding) :
    B₂.compactStabilizer (Φ q) = B₁.compactStabilizer q := by
  change rationalCommonNormKernel G ⊓ B₂.fixer (Φ q) =
    rationalCommonNormKernel G ⊓ B₁.fixer q
  rw [fixer_eq_of_equivariantEquiv B₁ B₂ Φ hΦ]

/-- KP Axiom 4.1.2 is invariant under the equivariant comparison. The
canonical `rationalPointTopology F G.X` and algebraic boundedness predicate
are literally the same on both sides. -/
theorem hasBoundedOpenStabilizers_iff_of_equivariantEquiv :
    B₂.HasBoundedOpenStabilizers ↔ B₁.HasBoundedOpenStabilizers := by
  constructor
  · intro h q
    have hq := h (Φ q)
    simpa only [compactStabilizer_eq_of_equivariantEquiv B₁ B₂ Φ hΦ q] using hq
  · intro h q
    have hK : B₂.compactStabilizer q = B₁.compactStabilizer (Φ.symm q) := by
      simpa only [Equiv.apply_symm_apply] using
        compactStabilizer_eq_of_equivariantEquiv B₁ B₂ Φ hΦ (Φ.symm q)
    simpa only [hK] using h (Φ.symm q)

end Equivariant

section ApartmentFacets

variable (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hmap : ∀ x : B₁.Apartment, Φ (B₁.apartmentMap x) = B₂.apartmentMap (e x))
  (hroots : AffineRootSystem.transportedRoots e B₁.affineRoots = B₂.affineRoots)
  (hiso : IsBuildingIso B₁ B₂ Φ)

include Φ e hmap hroots hiso

/-- AS 6 transfers through the full affine-root and building-facet
comparison. Injectivity of the target apartment map is proved here. -/
theorem hasCompatibleApartmentFacets_of_buildingIso
    (hB : B₁.HasCompatibleApartmentFacets) : B₂.HasCompatibleApartmentFacets where
  injective := by
    intro x y hxy
    have heq : Φ (B₁.apartmentMap (e.symm x)) =
        Φ (B₁.apartmentMap (e.symm y)) := by
      simpa only [hmap, e.apply_symm_apply] using hxy
    have hxy' := hB.injective (Φ.injective heq)
    exact e.symm.injective hxy'
  exists_isFacet_of_isFacet Y hY hmeet := by
    let Y₁ : Set B₁.ReducedBuilding := Φ ⁻¹' Y
    have himage : Φ '' Y₁ = Y := Set.image_preimage_eq _ Φ.surjective
    have hY₁ : B₁.IsFacet Y₁ := (hiso.isFacet_image_iff Y₁).1 (himage ▸ hY)
    obtain ⟨q, hqY, x, hxq⟩ := hmeet
    have hmeet₁ : (Y₁ ∩ B₁.apartmentImage).Nonempty := by
      refine ⟨B₁.apartmentMap (e.symm x), ?_, e.symm x, rfl⟩
      change Φ (B₁.apartmentMap (e.symm x)) ∈ Y
      rw [hmap, e.apply_symm_apply, hxq]
      exact hqY
    obtain ⟨Fa, hFa, hYFa⟩ := hB.exists_isFacet_of_isFacet Y₁ hY₁ hmeet₁
    refine ⟨e '' Fa,
      (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq e hroots Fa).2 hFa, ?_⟩
    rw [← himage, hYFa, Set.image_image, Set.image_image]
    congr 1
    funext x
    exact hmap x

end ApartmentFacets

end Langlands.Geometry.Building.ValuationBuildingData
