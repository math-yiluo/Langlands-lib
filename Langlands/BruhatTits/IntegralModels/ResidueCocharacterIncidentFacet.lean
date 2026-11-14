import Langlands.Geometry.Building.IncidentCocharacterFacet
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerResidueRoots

/-! # Incident facets for prescribed residue-torus cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {v : Valuation K (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)
    {N : IntegralModel R K G} (A : IntegralSplitTorusData N B.i)

/-- The generic lift of a prescribed residue cocharacter gives a short
incident ray whose vanishing-root signs and nonnegative fixers are
controlled by the actual residue lattice pairing. -/
theorem exists_pos_incidentFacet_of_specialFibreCocharacter (x : B.Apartment)
    (ν : cocharacterLattice A.specialFibreTorus) :
    let w := B.cocharacterDirection (A.cocharacterSpecialization.symm ν)
    ∃ ε : ℝ, 0 < ε ∧
      AffineRootSystem.IsFaceOf B.affineRoots
        (AffineRootSystem.facet B.affineRoots x)
        (AffineRootSystem.facet B.affineRoots (ε • w +ᵥ x)) ∧
      (∀ (a : relativeRoots B.i) (ψ : B.Apartment →ᵃ[ℝ] ℝ),
        ψ ∈ AffineRootSystem.vanishingRoots B.affineRoots x →
        ψ.linear = rootForm B.i a →
        SignType.sign (ψ (ε • w +ᵥ x)) =
          SignType.sign (latticePairing A.specialFibreTorus
            (A.characterSpecialization a) ν : ℝ)) ∧
      ∀ a : relativeRoots B.i,
        0 ≤ latticePairing A.specialFibreTorus (A.characterSpecialization a) ν →
        B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots x) =
          B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots (ε • w +ᵥ x)) := by
  dsimp only
  have hpair (a : relativeRoots B.i) :
      latticePairing B.S a (A.cocharacterSpecialization.symm ν) =
        latticePairing A.specialFibreTorus (A.characterSpecialization a) ν := by
    simpa only [AddEquiv.apply_symm_apply] using
      (A.latticePairing_specialization a (A.cocharacterSpecialization.symm ν)).symm
  obtain ⟨ε, hε, hface, hsign, hfix⟩ :=
    B.exists_pos_incidentFacet_of_cocharacter x (A.cocharacterSpecialization.symm ν)
  refine ⟨ε, hε, hface, ?_, ?_⟩
  · intro a ψ hψ hlin
    rw [hsign ψ hψ, hlin, B.rootForm_cocharacterDirection, hpair a]
  · intro a ha
    exact hfix a ((hpair a).symm ▸ ha)

/-- Every cocharacter of the actual special-fibre torus is realized by
an incident apartment facet with the prescribed nonnegative-root fixer
comparisons. -/
def HasSpecialFibreCocharacterIncidentFacets : Prop :=
  ∀ (x : B.Apartment) (ν : cocharacterLattice A.specialFibreTorus),
    ∃ C : Set B.Apartment, AffineRootSystem.IsFacet B.affineRoots C ∧
      AffineRootSystem.IsFaceOf B.affineRoots (AffineRootSystem.facet B.affineRoots x) C ∧
      ∀ a : relativeRoots B.i,
        0 ≤ latticePairing A.specialFibreTorus (A.characterSpecialization a) ν →
        B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots x) =
          B.apartment.rootFixer a C

theorem hasSpecialFibreCocharacterIncidentFacets :
    A.HasSpecialFibreCocharacterIncidentFacets B := by
  intro x ν
  obtain ⟨ε, _, hface, _, hfix⟩ :=
    A.exists_pos_incidentFacet_of_specialFibreCocharacter B x ν
  exact ⟨_, AffineRootSystem.isFacet_facet _ _, hface, hfix⟩

end Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData
