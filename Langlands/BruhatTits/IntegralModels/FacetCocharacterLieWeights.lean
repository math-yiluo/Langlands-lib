import Langlands.BruhatTits.IntegralModels.FacetAxioms
import Langlands.BruhatTits.IntegralModels.FacetCocharacterRay
import Langlands.BruhatTits.IntegralModels.FacetCocharacterSupport

/-! # Integral cocharacter supports from supplied facet Lie-weight formulas -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G) {x : B.Apartment}

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G} {j : B.S.toGrp ⟶ G}
  (T : IntegralTorusData D B.S j)

/-- Specialize the genuine integral cocharacter of the original incident
facet through the supplied integral split torus. -/
def incidentFacetSpecialCocharacter (hT : IsSplitTorus T.torus.toGrp)
    (F : IncidentAffineFacet B.affineRoots x) : cocharacterLattice T.specialFibre :=
  T.cocharacterSpecialization hT (incidentFacetCocharacter B F)

/-- Pairing with the specialized cocharacter is computed in the original
generic lattice using the character identification from the same torus. -/
theorem latticePairing_incidentFacetSpecialCocharacter
    (hT : IsSplitTorus T.torus.toGrp) (F : IncidentAffineFacet B.affineRoots x)
    (χ : characterLattice T.specialFibre) :
    latticePairing T.specialFibre χ (T.incidentFacetSpecialCocharacter B hT F) =
      latticePairing B.S ((T.characterSpecialization hT).symm χ)
        (incidentFacetCocharacter B F) := by
  simpa only [incidentFacetSpecialCocharacter, AddEquiv.apply_symm_apply] using
    T.latticePairing_specialization hT ((T.characterSpecialization hT).symm χ)
      (incidentFacetCocharacter B F)

end IntegralTorusData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)
  {j : B.S.toGrp ⟶ G} (T : IntegralTorusData source B.S j)

local instance cocharacterLieWeights_neutralSpecialFibre_affine
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance cocharacterLieWeights_neutralSpecialFibre_isAffine
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

local instance cocharacterLieWeights_quotient_isAffine : IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

/-- The supplied sign formula on an actual incident facet becomes integral
nonnegative-root support for the specialized genuine cocharacter. -/
theorem nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter
    (hT : IsSplitTorus T.torus.toGrp) (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite)
    (hsign : φ.HasApartmentLieWeightSignFormula B Q T hT
      (facet B.affineRoots x) F.val) :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ latticePairing T.specialFibre χ (T.incidentFacetSpecialCocharacter B hT F)} := by
  rw [hsign x (mem_facet_self _ _) (incidentFacetCocharacterRayVector B F hfinite)
    (incidentFacetCocharacterRayVector_mem B F hfinite)]
  ext χ
  simp only [Set.mem_ofPred_eq, T.latticePairing_incidentFacetSpecialCocharacter,
    eval_incidentFacetCocharacterRayVector_nonneg_iff]

/-- Apartment axioms discharge the individual finite-segment hypothesis in
the conversion from the supplied real sign formula to integral support. -/
theorem nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter_of_apartmentAxioms
    (hD : B.SatisfiesApartmentAxioms)
    (hT : IsSplitTorus T.torus.toGrp) (F : IncidentAffineFacet B.affineRoots x)
    (hsign : φ.HasApartmentLieWeightSignFormula B Q T hT
      (facet B.affineRoots x) F.val) :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ latticePairing T.specialFibre χ (T.incidentFacetSpecialCocharacter B hT F)} :=
  φ.nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter B Q T hT F
    (hD.isAffineRootSystem_affineRoots.finite_segment_roots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)) hsign

/-- With the actual quotient-root identification also supplied, pullback to
the generic character lattice recovers the existing geometric facet support. -/
theorem preimage_nonzeroLieImageWeights_eq_incidentFacetRootSupport
    (hT : IsSplitTorus T.torus.toGrp) (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite)
    (hsign : φ.HasApartmentLieWeightSignFormula B Q T hT
      (facet B.affineRoots x) F.val)
    (hroots : relativeRoots (φ.quotientTorusInclusion Q T) =
      T.characterSpecialization hT '' facetDerivativeRoots B (facet B.affineRoots x)) :
    T.characterSpecialization hT ⁻¹'
        nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      incidentFacetRootSupport B F := by
  rw [φ.nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter B Q T hT F hfinite hsign]
  ext χ
  change (_ ∧ _) ↔ (χ ∈ facetDerivativeRoots B (facet B.affineRoots x) ∧ _)
  rw [T.latticePairing_incidentFacetSpecialCocharacter]
  simp only [AddEquiv.symm_apply_apply, hroots, Set.mem_image,
    (T.characterSpecialization hT).injective.eq_iff, exists_eq_right]

/-- The original-apartment sign clause has the same integral consequence. -/
theorem nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter_of_signs
    (T₀ : IntegralTorusData source B.S B.i)
    (hT : IsSplitTorus T₀.torus.toGrp) (F : IncidentAffineFacet B.affineRoots x)
    (hfinite : (segmentRoots B.affineRoots x
      ((Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
        TranslationSpace B.i) +ᵥ x)).Finite)
    (hsign : φ.HasLieWeightSignFormula B Q T₀ hT
      (facet B.affineRoots x) F.val) :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T₀) (φ.reductiveImageInclusion Q) =
      {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T₀) ∧
        0 ≤ latticePairing T₀.specialFibre χ (T₀.incidentFacetSpecialCocharacter B hT F)} :=
  φ.nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter B Q T₀ hT F hfinite hsign

end RelativeComponentModelHom
end Langlands.BruhatTits.IntegralModels
