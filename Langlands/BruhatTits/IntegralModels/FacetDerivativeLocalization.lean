import Langlands.BruhatTits.IntegralModels.FacetRootDatum
import Langlands.Geometry.Building.AffineFacetDerivativeLocalization
import Langlands.GroupScheme.Rational.FiniteCharacterSignRealization
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Actual facet derivative roots and integral cocharacter representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building Geometry.Building.AffineRootSystem
open GroupScheme.RealTorusSpace

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The existing facet-root predicate is exactly the derivative image of
actual affine roots through a representative of that facet. -/
theorem mem_facetDerivativeRoots_facet_iff (x : B.Apartment) (a : relativeRoots B.i) :
    a.val ∈ facetDerivativeRoots B (facet B.affineRoots x) ↔
      rootForm B.i a ∈ derivativeRoots (vanishingRoots B.affineRoots x) := by
  constructor
  · rintro ⟨ha, ψ, hψ, hlin, hzero⟩
    exact ⟨ψ, ⟨hψ, hzero x (mem_facet_self _ _)⟩, hlin⟩
  · rintro ⟨ψ, hψ, hlin⟩
    exact ⟨a.property, ψ, hψ.1, hlin, facet_subset_hyperplane hψ⟩

/-- Every derivative form comes from an actual character in the existing
facet derivative-root set, and conversely. -/
theorem image_rootForm_facetDerivativeRoots (x : B.Apartment) :
    rootForm B.i '' {a : relativeRoots B.i |
      a.val ∈ facetDerivativeRoots B (facet B.affineRoots x)} =
        derivativeRoots (vanishingRoots B.affineRoots x) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact (mem_facetDerivativeRoots_facet_iff B x a).mp ha
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨a, hlin, _⟩ := hψ.1
    exact ⟨a, (mem_facetDerivativeRoots_facet_iff B x a).mpr ⟨ψ, hψ, hlin⟩,
      hlin.symm⟩

/-- Every facet of the actual derivative arrangement contains the projection
of a genuine integral cocharacter. -/
theorem exists_cocharacter_mem_derivativeFacet (x : B.Apartment)
    {C : Set (TranslationSpace B.i)}
    (hC : IsFacet (linearRootArrangement
      (derivativeRoots (vanishingRoots B.affineRoots x))) C) :
    ∃ μ : cocharacterLattice B.S,
      (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ) : TranslationSpace B.i) ∈ C := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hfinite : (relativeRoots B.i).Finite :=
    B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i
  obtain ⟨w, rfl⟩ := hC
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (rootAnnihilator B.i) w
  obtain ⟨μ, hμ⟩ := exists_cocharacter_sign_eq_on_finite hfinite v
  refine ⟨μ, ?_⟩
  rintro η ⟨f, ⟨ψ, hψ, rfl⟩, rfl⟩
  obtain ⟨a, hlin, _⟩ := hψ.1
  change SignType.sign (ψ.linear (Submodule.Quotient.mk v)) =
    SignType.sign (ψ.linear (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] μ)))
  rw [hlin, rootForm_mk, rootForm_mk, eval_tmul, one_mul, sign_intCast]
  exact (hμ a.val a.property).symm

/-- A chosen integral cocharacter in the supplied actual derivative facet. -/
def derivativeFacetCocharacter (x : B.Apartment)
    (C : {C : Set (TranslationSpace B.i) // IsFacet (linearRootArrangement
      (derivativeRoots (vanishingRoots B.affineRoots x))) C}) :
    cocharacterLattice B.S :=
  (exists_cocharacter_mem_derivativeFacet B x C.property).choose

theorem derivativeFacetCocharacter_mem (x : B.Apartment)
    (C : {C : Set (TranslationSpace B.i) // IsFacet (linearRootArrangement
      (derivativeRoots (vanishingRoots B.affineRoots x))) C}) :
    (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] derivativeFacetCocharacter B x C) :
      TranslationSpace B.i) ∈ C.val :=
  (exists_cocharacter_mem_derivativeFacet B x C.property).choose_spec

/-- A genuine integral cocharacter representing the derivative facet of an
original incident full facet. -/
def incidentFacetCocharacter {x : B.Apartment}
    (F : IncidentAffineFacet B.affineRoots x) : cocharacterLattice B.S :=
  derivativeFacetCocharacter B x (incidentFacetDerivative F)

theorem incidentFacetCocharacter_mem {x : B.Apartment}
    (F : IncidentAffineFacet B.affineRoots x) :
    (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] incidentFacetCocharacter B F) :
      TranslationSpace B.i) ∈ (incidentFacetDerivative F).val :=
  derivativeFacetCocharacter_mem B x (incidentFacetDerivative F)

end Langlands.BruhatTits.IntegralModels
