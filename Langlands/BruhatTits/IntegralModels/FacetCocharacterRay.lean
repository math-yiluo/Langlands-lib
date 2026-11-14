import Langlands.BruhatTits.IntegralModels.FacetDerivativeLocalization
import Langlands.Geometry.Building.AffineIncidentFacetRay

/-! # Actual cocharacter rays reaching original incident facets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem
open GroupScheme.RealTorusSpace

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G) {x : B.Apartment}

private theorem projected_tmul_eq_smul (μ : cocharacterLattice B.S) (t : ℝ) :
    (Submodule.Quotient.mk (t ⊗ₜ[ℤ] μ) : TranslationSpace B.i) =
      t • (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ) : TranslationSpace B.i) := by
  rw [← Submodule.Quotient.mk_smul]
  simp only [smul_tmul', smul_eq_mul, mul_one]

/-- The chosen genuine integral cocharacter reaches the original full facet
along every sufficiently short positive scalar of its tensor ray. -/
theorem eventually_pos_cocharacterRay_mem
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (Submodule.Quotient.mk (t ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x ∈ F.val := by
  filter_upwards [eventually_pos_smul_vadd_mem_incidentFacet F _
    (incidentFacetCocharacter_mem B F) hfinite] with t ht
  rw [projected_tmul_eq_smul]
  exact ht

/-- A positive scalar less than one on the actual integral cocharacter ray. -/
def incidentFacetCocharacterRayParameter
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite) : ℝ :=
  incidentFacetRayParameter F _ (incidentFacetCocharacter_mem B F) hfinite

theorem incidentFacetCocharacterRayParameter_spec
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite) :
    0 < incidentFacetCocharacterRayParameter B F hfinite ∧
      incidentFacetCocharacterRayParameter B F hfinite < 1 ∧
      (Submodule.Quotient.mk
        (incidentFacetCocharacterRayParameter B F hfinite ⊗ₜ[ℤ]
          incidentFacetCocharacter B F) : TranslationSpace B.i) +ᵥ x ∈ F.val := by
  have h := incidentFacetRayParameter_spec F _ (incidentFacetCocharacter_mem B F) hfinite
  refine ⟨h.1, h.2.1, ?_⟩
  rw [projected_tmul_eq_smul]
  exact h.2.2

/-- The real tensor vector on the chosen integral cocharacter ray whose
projection translates the base point into the original full facet. -/
def incidentFacetCocharacterRayVector
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite) : RealTorusSpace.V B.S :=
  incidentFacetCocharacterRayParameter B F hfinite ⊗ₜ[ℤ] incidentFacetCocharacter B F

theorem incidentFacetCocharacterRayVector_mem
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite) :
    (Submodule.Quotient.mk (incidentFacetCocharacterRayVector B F hfinite) :
      TranslationSpace B.i) +ᵥ x ∈ F.val :=
  (incidentFacetCocharacterRayParameter_spec B F hfinite).2.2

/-- Every actual character has the same sign on the short real ray vector as
its integer pairing with the original chosen integral cocharacter. -/
theorem sign_eval_incidentFacetCocharacterRayVector
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite)
    (χ : characterLattice B.S) :
    SignType.sign (eval B.S χ (incidentFacetCocharacterRayVector B F hfinite)) =
      SignType.sign (latticePairing B.S χ (incidentFacetCocharacter B F)) := by
  rw [incidentFacetCocharacterRayVector, eval_tmul, sign_mul,
    sign_pos (incidentFacetCocharacterRayParameter_spec B F hfinite).1,
    one_mul, sign_intCast]

theorem eval_incidentFacetCocharacterRayVector_nonneg_iff
    (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite)
    (χ : characterLattice B.S) :
    0 ≤ eval B.S χ (incidentFacetCocharacterRayVector B F hfinite) ↔
      0 ≤ latticePairing B.S χ (incidentFacetCocharacter B F) := by
  rw [incidentFacetCocharacterRayVector, eval_tmul,
    mul_nonneg_iff_of_pos_left (incidentFacetCocharacterRayParameter_spec B F hfinite).1,
    Int.cast_nonneg_iff]

/-- The supplied apartment axioms provide the finite separation required for
an actual cocharacter ray to reach each original incident facet. -/
theorem exists_pos_cocharacterRay_mem_of_apartmentAxioms
    (hD : B.SatisfiesApartmentAxioms) (F : IncidentAffineFacet B.affineRoots x) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (Submodule.Quotient.mk (t ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x ∈ F.val := by
  let hfinite := hD.isAffineRootSystem_affineRoots.finite_segment_roots x
    ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
      TranslationSpace B.i) +ᵥ x)
  exact ⟨incidentFacetCocharacterRayParameter B F hfinite,
    incidentFacetCocharacterRayParameter_spec B F hfinite⟩

end Langlands.BruhatTits.IntegralModels
