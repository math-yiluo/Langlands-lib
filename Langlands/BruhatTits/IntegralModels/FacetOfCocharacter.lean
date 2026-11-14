import Langlands.BruhatTits.IntegralModels.FacetCocharacterSupport

/-! # Original incident facets realizing arbitrary cocharacter supports -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem
open GroupScheme.RealTorusSpace

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G) (x : B.Apartment)

/-- Apply the inverse of the actual derivative-facet equivalence to the
derivative facet containing the projected supplied integral cocharacter. -/
def incidentFacetOfCocharacter
    (hfinite : ∀ y : B.Apartment, (segmentRoots B.affineRoots x y).Finite)
    (μ : cocharacterLattice B.S) : IncidentAffineFacet B.affineRoots x :=
  (incidentFacetDerivativeOrderIso hfinite).toEquiv.symm
    ⟨facet (linearRootArrangement (derivativeRoots (vanishingRoots B.affineRoots x)))
      (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ) : TranslationSpace B.i),
      isFacet_facet _ _⟩

/-- The inverse construction retains exactly the supplied cocharacter's
actual derivative sign facet. -/
theorem incidentFacetDerivative_incidentFacetOfCocharacter
    (hfinite : ∀ y : B.Apartment, (segmentRoots B.affineRoots x y).Finite)
    (μ : cocharacterLattice B.S) :
    (incidentFacetDerivative (incidentFacetOfCocharacter B x hfinite μ)).val =
      facet (linearRootArrangement (derivativeRoots (vanishingRoots B.affineRoots x)))
        (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ) : TranslationSpace B.i) :=
  congrArg Subtype.val ((incidentFacetDerivativeOrderIso hfinite).toEquiv.apply_symm_apply _)

/-- Every actual derivative character has the same pairing sign on the
chosen representative of this facet as on the originally supplied cocharacter. -/
theorem sign_latticePairing_incidentFacetOfCocharacter
    (hfinite : ∀ y : B.Apartment, (segmentRoots B.affineRoots x y).Finite)
    (μ : cocharacterLattice B.S) (χ : characterLattice B.S)
    (hχ : χ ∈ facetDerivativeRoots B (facet B.affineRoots x)) :
    SignType.sign (latticePairing B.S χ
      (incidentFacetCocharacter B (incidentFacetOfCocharacter B x hfinite μ))) =
        SignType.sign (latticePairing B.S χ μ) := by
  let a : relativeRoots B.i := ⟨χ, hχ.choose⟩
  have ha : rootForm B.i a ∈ derivativeRoots (vanishingRoots B.affineRoots x) :=
    (mem_facetDerivativeRoots_facet_iff B x a).mp hχ
  have hw := incidentFacetCocharacter_mem B (incidentFacetOfCocharacter B x hfinite μ)
  rw [incidentFacetDerivative_incidentFacetOfCocharacter] at hw
  have hsign := hw (rootForm B.i a).toAffineMap ⟨rootForm B.i a, ha, rfl⟩
  change SignType.sign
      (rootForm B.i a (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ))) =
    SignType.sign (rootForm B.i a (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ]
      incidentFacetCocharacter B (incidentFacetOfCocharacter B x hfinite μ)))) at hsign
  simp only [rootForm_mk, eval_tmul, one_mul, sign_intCast] at hsign
  exact hsign.symm

/-- The original full incident facet realizes precisely the actual
derivative characters with nonnegative pairing on the supplied cocharacter. -/
theorem incidentFacetRootSupport_incidentFacetOfCocharacter
    (hfinite : ∀ y : B.Apartment, (segmentRoots B.affineRoots x y).Finite)
    (μ : cocharacterLattice B.S) :
    incidentFacetRootSupport B (incidentFacetOfCocharacter B x hfinite μ) =
      {χ | χ ∈ facetDerivativeRoots B (facet B.affineRoots x) ∧
        0 ≤ latticePairing B.S χ μ} := by
  ext χ
  change (_ ∧ _) ↔ (_ ∧ _)
  refine and_congr_right fun hχ => ?_
  calc
    _ ↔ 0 ≤ SignType.sign (latticePairing B.S χ
        (incidentFacetCocharacter B (incidentFacetOfCocharacter B x hfinite μ))) :=
      sign_nonneg_iff.symm
    _ ↔ 0 ≤ SignType.sign (latticePairing B.S χ μ) := by
      rw [sign_latticePairing_incidentFacetOfCocharacter B x hfinite μ χ hχ]
    _ ↔ _ := sign_nonneg_iff

/-- Supplied apartment axioms realize every integral cocharacter support
by an original incident full facet. -/
theorem exists_incidentFacetRootSupport_eq_of_apartmentAxioms
    (hD : B.SatisfiesApartmentAxioms) (μ : cocharacterLattice B.S) :
    ∃ F : IncidentAffineFacet B.affineRoots x,
      incidentFacetRootSupport B F =
        {χ | χ ∈ facetDerivativeRoots B (facet B.affineRoots x) ∧
          0 ≤ latticePairing B.S χ μ} :=
  ⟨incidentFacetOfCocharacter B x
      (hD.isAffineRootSystem_affineRoots.finite_segment_roots x) μ,
    incidentFacetRootSupport_incidentFacetOfCocharacter B x _ μ⟩

end Langlands.BruhatTits.IntegralModels
