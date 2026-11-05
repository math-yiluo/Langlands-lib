import Langlands.Geometry.Building.AffineChamberFreeness
import Langlands.Geometry.Building.AffineReflectionGalleryGeometry
import Langlands.Geometry.Building.ReflectionGalleryFreeness

/-! # Simple transitivity of the actual affine Weyl action on chambers -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Corrected AR4 implies the pointwise local finiteness required by the
generic reflection-arrangement geometry. -/
theorem IsAffineRootSystemWithRankZero.isLocallyFiniteReflectionArrangement
    (hΨ : IsAffineRootSystemWithRankZero Ψ) :
    IsLocallyFiniteReflectionArrangement Ψ where
  span_derivativeRoots_eq_top := hΨ.span_derivativeRoots_eq_top
  linear_ne_zero := hΨ.linear_ne_zero
  finite_derivativeRoots := hΨ.finite_derivativeRoots
  exists_isCoroot := hΨ.exists_isCoroot
  finite_bounded_at := hΨ.finite_bounded_at

end AffineRootSystem

open AffineRootSystem

/-- The exact global chamber conclusion follows from the two generic gallery
prerequisites, with their full hypotheses discharged for the actual action. -/
theorem affineChamberSimpleTransitivity_of_gallery
    (hgeometry : AffineReflectionGalleryGeometryStatement.{uV, uA})
    (hfree : ReflectionGallery.ReflectionGalleryFreenessStatement.{max uV uA, uA}) :
    AffineChamberSimpleTransitivityStatement.{uV, uA} := by
  intro V A _ _ _ Ψ hΨ C D hC hD
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, rfl⟩ := hD
  obtain ⟨hgen, htransport⟩ :=
    hgeometry V A Ψ hΨ.isLocallyFiniteReflectionArrangement x hx
  obtain ⟨w, hw⟩ := htransport y hy
  let w' : affineWeylGroup Ψ := ⟨(w : A ≃ᵃ[ℝ] A), hgen ▸ w.property⟩
  have himage : (w' : A ≃ᵃ[ℝ] A) '' facet Ψ x = facet Ψ y := by
    rw [image_facet
      (affineWeylGroup_le_rootStabilizer Ψ w'.property)]
    exact facet_eq_facet_iff.2 hw
  refine ⟨w', himage, ?_⟩
  intro v hv
  have hfix :
      ((w'⁻¹ * v : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) '' facet Ψ x =
        facet Ψ x := by
    change ((w' : A ≃ᵃ[ℝ] A)⁻¹ * (v : A ≃ᵃ[ℝ] A)) '' facet Ψ x =
      facet Ψ x
    calc
      _ = (w' : A ≃ᵃ[ℝ] A).symm '' ((v : A ≃ᵃ[ℝ] A) '' facet Ψ x) := by
        rw [AffineEquiv.coe_mul, AffineEquiv.inv_def]
        exact (Set.image_image (w' : A ≃ᵃ[ℝ] A).symm
          (v : A ≃ᵃ[ℝ] A) (facet Ψ x)).symm
      _ = (w' : A ≃ᵃ[ℝ] A).symm '' ((w' : A ≃ᵃ[ℝ] A) '' facet Ψ x) := by
        rw [hv, himage]
      _ = facet Ψ x := by
        rw [Set.image_image]
        simp only [AffineEquiv.symm_apply_apply]
        exact Set.image_id _
  have heq := chamber_stabilizer_eq_one hfree
    (⟨facet Ψ x, ⟨x, hx, rfl⟩⟩ : Chambers Ψ)
    (mem_facet_self Ψ x) hgen (w'⁻¹ * v) hfix
  exact (inv_mul_eq_one.mp heq).symm

/-- The actual affine Weyl group acts simply transitively on its chambers,
including nonreduced systems and rank zero. -/
theorem affineChamberSimpleTransitivity :
    AffineChamberSimpleTransitivityStatement.{uV, uA} :=
  affineChamberSimpleTransitivity_of_gallery
    affineReflectionGalleryGeometry.{uV, uA}
    ReflectionGallery.reflectionGalleryFreeness.{max uV uA, uA}

end Langlands.Geometry.Building
