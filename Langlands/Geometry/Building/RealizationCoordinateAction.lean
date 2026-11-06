import Langlands.Geometry.Building.PolysimplicialCoordinateFibers
import Langlands.Geometry.Building.RealizationVertexAction

/-! # Coordinate-fiber criterion for the original quotient action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData.PolysimplicialRealization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G} (R : B.PolysimplicialRealization)

theorem vertexTranslateEquiv_image_mem_facets (hR : R.IsFaceCompatible)
    (g : rationalPoints G) {A : Set (∀ i, R.V i)} (hA : A ∈ R.complex.facets) :
    R.vertexTranslateEquiv hR g '' A ∈ R.complex.facets := by
  have H := R.vertexTranslateEquiv_image hR g ⟨A, hA⟩
  rw [H]
  exact (R.facetTranslateOrderIso hR g ⟨A, hA⟩).property

theorem vertexTranslateEquiv_preimage_mem_facets (hR : R.IsFaceCompatible)
    (g : rationalPoints G) {A : Set (∀ i, R.V i)} (hA : A ∈ R.complex.facets) :
    R.vertexTranslateEquiv hR g ⁻¹' A ∈ R.complex.facets := by
  rw [← (R.vertexTranslateEquiv hR g).image_symm_eq_preimage,
    ← R.vertexTranslateEquiv_inv hR g]
  exact R.vertexTranslateEquiv_image_mem_facets hR g⁻¹ hA

/-- A supplied coordinate permutation and fiber condition upgrade the canonical vertex
action to the existing notion of polysimplicial isomorphism. -/
def polysimplicialTranslateIso (hR : R.IsFaceCompatible) (g : rationalPoints G)
    (σ : Equiv.Perm R.index)
    (he : AbstractBuilding.RespectsCoordinateFibers σ (R.vertexTranslateEquiv hR g)) :
    AbstractBuilding.PolysimplicialIso R.complex R.complex :=
  he.toPolysimplicialIso
    (fun _ hA => R.vertexTranslateEquiv_image_mem_facets hR g hA)
    (fun _ hA => R.vertexTranslateEquiv_preimage_mem_facets hR g hA)
    (fun i => Classical.choice (R.complex.factor i).nonempty_vertices)

theorem polysimplicialTranslateIso_vertexEquiv (hR : R.IsFaceCompatible)
    (g : rationalPoints G) (σ : Equiv.Perm R.index)
    (he : AbstractBuilding.RespectsCoordinateFibers σ (R.vertexTranslateEquiv hR g)) :
    (R.polysimplicialTranslateIso hR g σ he).vertexEquiv = R.vertexTranslateEquiv hR g :=
  he.toPolysimplicialIso_vertexEquiv _ _ _

theorem polysimplicialTranslateIso_image_iff (hR : R.IsFaceCompatible)
    (g : rationalPoints G) (σ : Equiv.Perm R.index)
    (he : AbstractBuilding.RespectsCoordinateFibers σ (R.vertexTranslateEquiv hR g))
    (Fc Fc' : R.complex.facets) :
    Fc'.val = (R.polysimplicialTranslateIso hR g σ he).vertexEquiv '' Fc.val ↔
      (R.realize Fc').val =
        (fun y : B.ReducedBuilding => g • y) '' (R.realize Fc).val := by
  rw [R.polysimplicialTranslateIso_vertexEquiv]
  exact R.vertexTranslateEquiv_image_iff hR g Fc Fc'

/-- The canonical action already preserves facets; only coordinate compatibility remains. -/
theorem isPolysimplicialAction_iff_respectsCoordinateFibers (hR : R.IsFaceCompatible) :
    R.IsPolysimplicialAction ↔
      ∀ g : rationalPoints G, ∃ σ : Equiv.Perm R.index,
        AbstractBuilding.RespectsCoordinateFibers σ (R.vertexTranslateEquiv hR g) := by
  rw [R.isPolysimplicialAction_iff_vertexTranslateEquiv hR]
  exact forall_congr' fun g =>
    AbstractBuilding.isPolysimplicialAutomorphism_iff_respectsCoordinateFibers R.complex
      (R.vertexTranslateEquiv hR g)
      (fun _ hA => R.vertexTranslateEquiv_image_mem_facets hR g hA)
      (fun _ hA => R.vertexTranslateEquiv_preimage_mem_facets hR g hA)

end Langlands.Geometry.Building.ValuationBuildingData.PolysimplicialRealization
