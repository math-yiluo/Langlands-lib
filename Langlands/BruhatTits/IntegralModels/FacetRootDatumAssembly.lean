import Langlands.BruhatTits.IntegralModels.FacetAxioms
import Langlands.GroupScheme.Reductive.RootDatumFiniteWeylAssembly

/-! # Assembling a facet root datum from quotient roots and reflections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  {D : RelativeComponentModelData R K G}
  (Q : SpecialFibreQuotientData D)
  {j : B.S.toGrp ⟶ G} (T : IntegralTorusData D B.S j)
  (Droot : RelativeRootReflectionData B.i)

variable
    (hT : IsSplitTorus T.torus.toGrp) (Fa : Set B.Apartment)
    (hQ : IsConnectedReductive Q.quotient)
    (hclosed : IsClosedSubgroup (T.specialFibreInclusion ≫ Q.projection))
    (hroots : ∀ χ : characterLattice T.specialFibre,
      χ ∈ relativeRoots (T.specialFibreInclusion ≫ Q.projection) ↔
        (T.characterSpecialization hT).symm χ ∈ facetDerivativeRoots B Fa)
    (hreflections : ∀ a : relativeRoots B.i, a.val ∈ facetDerivativeRoots B Fa →
      ∃ (n : rationalPoints Q.quotient) (σ : T.specialFibre ≅ T.specialFibre),
        IsNormalizingPoint (T.specialFibreInclusion ≫ Q.projection) n σ ∧
          ∀ χ : characterLattice T.specialFibre,
            characterAut σ χ =
              χ - latticePairing T.specialFibre χ
                (T.cocharacterSpecialization hT (Droot.coroot a)) •
                  T.characterSpecialization hT a.val)

include hQ hclosed hroots hreflections

/-- The actual quotient root datum, with its quotient interpretation and paired
derivative-graph equality, constructed from explicit geometric comparisons. -/
def apartmentDerivativeRootDatumOfRootComparison :
    {P : RootDatum (relativeRoots (T.specialFibreInclusion ≫ Q.projection))
        (characterLattice T.specialFibre) (cocharacterLattice T.specialFibre) //
      IsRootDatumOf (T.specialFibreInclusion ≫ Q.projection) P ∧
        Set.range (fun k => (P.root k, P.coroot k)) =
          apartmentDerivativeRootCorootGraph B T Droot hT Fa} := by
  classical
  let iQ := T.specialFibreInclusion ≫ Q.projection
  have : IsClosedImmersion iQ.hom.hom.left := hclosed
  have : Mono iQ.hom.hom.left := inferInstance
  have : Smooth Q.quotient.X.hom := hQ.smooth
  have hsplit : IsSplitTorus T.specialFibre.toGrp :=
    IsSplitTorus.baseChange (IntegralModel.residueBaseMap R) hT
  have : Finite (weylImage iQ) :=
    splitTorusWeylImageFinite (IsLocalRing.ResidueField R) Q.quotient
      T.specialFibre hsplit iQ hclosed
  have hfinite := hsplit.finite_relativeRoots iQ
  let originalRoot : relativeRoots iQ → relativeRoots B.i := fun α =>
    ⟨(T.characterSpecialization hT).symm α.val,
      ((hroots α.val).mp α.property).choose⟩
  have horiginal (α : relativeRoots iQ) :
      (originalRoot α).val ∈ facetDerivativeRoots B Fa :=
    (hroots α.val).mp α.property
  have hspecialize (α : relativeRoots iQ) :
      T.characterSpecialization hT (originalRoot α).val = α.val :=
    (T.characterSpecialization hT).apply_symm_apply α.val
  have hrepresentative (α : relativeRoots iQ) :=
    hreflections (originalRoot α) (horiginal α)
  choose n σ hn hσ using hrepresentative
  let DQ : RelativeRootReflectionData (T := T.specialFibre) iQ :=
    { coroot := fun α => T.cocharacterSpecialization hT (Droot.coroot (originalRoot α))
      representative := fun α => ⟨n α, σ α, hn α⟩
      pair_self := fun α => by
        rw [← hspecialize α, T.latticePairing_specialization, Droot.pair_self]
      action := fun α χ => by
        have hweyl :
            weylAction (T := T.specialFibre) iQ ⟨n α, σ α, hn α⟩ χ =
              characterAut (σ α) χ :=
          weylAction_eq (T := T.specialFibre) iQ
            (n := ⟨n α, σ α, hn α⟩) (σ := σ α) (hn α) χ
        exact hweyl.trans (by simpa only [hspecialize] using hσ α χ) }
  refine ⟨DQ.rootDatumOfFiniteWeylImage hsplit hfinite,
    DQ.isRootDatumOf_rootDatumOfFiniteWeylImage hsplit hfinite, ?_⟩
  change Set.range (fun α : relativeRoots iQ =>
    (α.val, T.cocharacterSpecialization hT (Droot.coroot (originalRoot α)))) =
      apartmentDerivativeRootCorootGraph B T Droot hT Fa
  ext p
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨originalRoot α, horiginal α, by rw [hspecialize]⟩
  · rintro ⟨a, ha, rfl⟩
    have hroot : T.characterSpecialization hT a.val ∈ relativeRoots iQ :=
      (hroots _).mpr (by simpa using ha)
    let α : relativeRoots iQ := ⟨T.characterSpecialization hT a.val, hroot⟩
    have horiginal_eq : originalRoot α = a := by
      apply Subtype.ext
      exact (T.characterSpecialization hT).symm_apply_apply a.val
    exact ⟨α, by change (α.val, _) = _; rw [horiginal_eq]⟩

/-- Exact quotient-root comparison and actual specialized reflection representatives
give the complete paired derivative root datum. The two geometric comparison
inputs are explicit; this theorem does not assert that they exist. -/
theorem hasApartmentDerivativeRootDatum_of_rootComparison :
    HasApartmentDerivativeRootDatum B Q T Droot hT Fa := by
  have : Smooth Q.quotient.X.hom := hQ.smooth
  have hsplit : IsSplitTorus T.specialFibre.toGrp :=
    IsSplitTorus.baseChange (IntegralModel.residueBaseMap R) hT
  let P := apartmentDerivativeRootDatumOfRootComparison B Q T Droot
    hT Fa hQ hclosed hroots hreflections
  exact ⟨relativeRoots (T.specialFibreInclusion ≫ Q.projection),
    (hsplit.finite_relativeRoots _).to_subtype, P.val, P.property⟩

end Langlands.BruhatTits.IntegralModels
