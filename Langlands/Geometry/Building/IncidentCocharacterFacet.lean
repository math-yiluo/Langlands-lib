import Langlands.Geometry.Building.AffineReflectionGalleryGeometry
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.IncidentFacetRootFiltration

/-! # Incident facets in prescribed cocharacter directions -/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A sufficiently short positive ray enters an incident facet, with the
signs of the roots vanishing at its origin prescribed by its direction. -/
theorem exists_pos_isFaceOf_facet_smul_vadd
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (x : A) (v : V) :
    ∃ ε : ℝ, 0 < ε ∧
      IsFaceOf Ψ (facet Ψ x) (facet Ψ (ε • v +ᵥ x)) ∧
      ∀ ψ ∈ vanishingRoots Ψ x,
        SignType.sign (ψ (ε • v +ᵥ x)) = SignType.sign (ψ.linear v) := by
  obtain ⟨ε, hε, hsign⟩ := exists_pos_of_eventually (eventually_sign_smul_vadd hΨ x v)
  refine ⟨ε, hε, ⟨isFacet_facet Ψ x, ε • v +ᵥ x, rfl, ?_⟩, ?_⟩
  · apply facet_subset_facetClosure_iff.mpr
    intro ψ hψ
    by_cases hx : ψ x = 0
    · exact Or.inl (by simp [hx])
    · exact Or.inr (hsign ψ hψ hx).symm
  · intro ψ hψ
    rw [GalleryGeometry.apply_smul_vadd, hψ.2, zero_add, sign_mul,
      sign_pos hε, one_mul]

end AffineRootSystem

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- The actual cocharacter direction in the reduced apartment. -/
def cocharacterDirection (ν : cocharacterLattice B.S) : TranslationSpace B.i :=
  Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)

@[simp] theorem rootForm_cocharacterDirection (a : relativeRoots B.i)
    (ν : cocharacterLattice B.S) :
    rootForm B.i a (B.cocharacterDirection ν) = (latticePairing B.S a ν : ℝ) := by
  simp [cocharacterDirection]

/-- Any prescribed actual cocharacter admits a short incident ray; every
root nonnegative on that cocharacter has unchanged nonstrict fixer. -/
theorem exists_pos_incidentFacet_of_cocharacter (x : B.Apartment)
    (ν : cocharacterLattice B.S) :
    ∃ ε : ℝ, 0 < ε ∧
      AffineRootSystem.IsFaceOf B.affineRoots
        (AffineRootSystem.facet B.affineRoots x)
        (AffineRootSystem.facet B.affineRoots (ε • B.cocharacterDirection ν +ᵥ x)) ∧
      (∀ ψ ∈ AffineRootSystem.vanishingRoots B.affineRoots x,
        SignType.sign (ψ (ε • B.cocharacterDirection ν +ᵥ x)) =
          SignType.sign (ψ.linear (B.cocharacterDirection ν))) ∧
      ∀ a : relativeRoots B.i, 0 ≤ latticePairing B.S a ν →
        B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots x) =
          B.apartment.rootFixer a
            (AffineRootSystem.facet B.affineRoots (ε • B.cocharacterDirection ν +ᵥ x)) := by
  obtain ⟨ε, hε, hface, hsign⟩ :=
    AffineRootSystem.exists_pos_isFaceOf_facet_smul_vadd
      (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
        B.hasOppositeFactorPairs) x (B.cocharacterDirection ν)
  refine ⟨ε, hε, hface, hsign, fun a ha => ?_⟩
  apply B.apartment.rootFixer_eq_of_incidentFacets_of_nonneg
    B.affineRoot_mem_or_two_smul_mem
    (AffineRootSystem.isFacet_facet _ _) hface
    (AffineRootSystem.mem_facet_self _ _) (AffineRootSystem.mem_facet_self _ _) a
  rw [vadd_vsub, map_smul, B.rootForm_cocharacterDirection, smul_eq_mul]
  exact mul_nonneg hε.le (by exact_mod_cast ha)

/-- Prescribed cocharacters determine incident facets with their nonnegative
root-fixer equalities, without a regularity or genericity hypothesis. -/
def HasPrescribedCocharacterIncidentFacets : Prop :=
  ∀ (x : B.Apartment) (ν : cocharacterLattice B.S),
    ∃ C : Set B.Apartment, AffineRootSystem.IsFacet B.affineRoots C ∧
      AffineRootSystem.IsFaceOf B.affineRoots (AffineRootSystem.facet B.affineRoots x) C ∧
      ∀ a : relativeRoots B.i, 0 ≤ latticePairing B.S a ν →
        B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots x) =
          B.apartment.rootFixer a C

theorem hasPrescribedCocharacterIncidentFacets :
    B.HasPrescribedCocharacterIncidentFacets := by
  intro x ν
  obtain ⟨ε, _, hface, _, hfix⟩ := B.exists_pos_incidentFacet_of_cocharacter x ν
  exact ⟨_, AffineRootSystem.isFacet_facet _ _, hface, hfix⟩

end IntegerValuationBuildingData

end Langlands.Geometry.Building
