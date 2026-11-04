import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Reductive.RootDatum

/-! # The derivative root datum of a facet in a supplied KP model

Both lattice identifications come from the same integral split torus.
The roots are derivatives of actual affine roots vanishing on the facet,
and the coroots are those of the original torus's integral reflection data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i)

/-- The canonical integral-to-generic cocharacter identification. -/
def genericCocharacterEquiv (hT : IsSplitTorus T.torus.toGrp) :
    cocharacterLattice T.torus ≃+ cocharacterLattice S :=
  (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) T.torus hT).trans
    (cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso T.genericIso))

/-- The canonical integral-to-special cocharacter identification. -/
def specialCocharacterEquiv (hT : IsSplitTorus T.torus.toGrp) :
    cocharacterLattice T.torus ≃+ cocharacterLattice T.specialFibre :=
  cocharacterLattice.baseChangeEquiv (IntegralModel.residueBaseMap R) T.torus hT

/-- The generic-to-special identification induced by the actual integral torus. -/
def cocharacterSpecialization (hT : IsSplitTorus T.torus.toGrp) :
    cocharacterLattice S ≃+ cocharacterLattice T.specialFibre :=
  (T.genericCocharacterEquiv hT).symm.trans (T.specialCocharacterEquiv hT)

omit [IsLocalRing R] in
/-- The generic-fibre identifications preserve the actual lattice pairing. -/
theorem latticePairing_generic (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice T.torus) (ν : cocharacterLattice T.torus) :
    latticePairing S (T.genericCharacterEquiv hT χ) (T.genericCocharacterEquiv hT ν) =
      latticePairing T.torus χ ν := by
  change latticePairing S
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso T.genericIso)
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ))
    (cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso T.genericIso)
      (cocharacterLattice.baseChange (Spec.algebraMap R K) T.torus ν)) = _
  rw [latticePairing_congr, latticePairing_baseChange]

/-- Specialization through the same integral torus preserves the pairing. -/
theorem latticePairing_specialization (hT : IsSplitTorus T.torus.toGrp)
    (χ : characterLattice S) (ν : cocharacterLattice S) :
    latticePairing T.specialFibre (T.characterSpecialization hT χ)
      (T.cocharacterSpecialization hT ν) = latticePairing S χ ν := by
  obtain ⟨χ₀, rfl⟩ := (T.genericCharacterEquiv hT).surjective χ
  obtain ⟨ν₀, rfl⟩ := (T.genericCocharacterEquiv hT).surjective ν
  rw [characterSpecialization, cocharacterSpecialization,
    AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  change latticePairing T.specialFibre
    (characterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus χ₀)
    (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus ν₀) = _
  rw [latticePairing_baseChange, T.latticePairing_generic]

end IntegralTorusData

section Facet

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsAffineHom G.X.hom]
  (B : Geometry.Building.ValuationBuildingData G)

/-- The derivative image of the affine roots vanishing identically on `F`,
expressed as actual characters of the original maximal split torus. -/
def facetDerivativeRoots (F : Set B.Apartment) : Set (characterLattice B.S) :=
  {a | ∃ ha : a ∈ relativeRoots B.i, ∃ ψ ∈ B.affineRoots,
    ψ.linear = Geometry.Building.rootForm B.i ⟨a, ha⟩ ∧ ∀ x ∈ F, ψ x = 0}

variable {source target : RelativeComponentModelData R K G}
  (T : IntegralTorusData source B.S B.i)
  (D : RelativeRootReflectionData B.i)

/-- The matching root-coroot pairs of the derivative subsystem, transported
by the actual integral split torus to its special-fibre lattices. -/
def facetDerivativeRootCorootGraph (hT : IsSplitTorus T.torus.toGrp)
    (F : Set B.Apartment) :
    Set (characterLattice T.specialFibre × cocharacterLattice T.specialFibre) :=
  {p | ∃ a : relativeRoots B.i, a.val ∈ facetDerivativeRoots B F ∧
    p = (T.characterSpecialization hT a.val, T.cocharacterSpecialization hT (D.coroot a))}

namespace RelativeComponentModelHom

variable (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)

/-- KP Axiom 4.1.22(6): the actual quotient's torus root datum has exactly the
derivative roots and their corresponding original coroots. The ambient validity
predicate supplies facets, reductive-quotient and maximal-torus conditions. -/
def HasFacetDerivativeRootDatum (hT : IsSplitTorus T.torus.toGrp)
    (F : Set B.Apartment) : Prop :=
  ∃ (J : Type u) (_ : Finite J)
    (P : RootDatum J (characterLattice T.specialFibre) (cocharacterLattice T.specialFibre)),
      IsRootDatumOf (φ.quotientTorusInclusion Q T) P ∧
        Set.range (fun j => (P.root j, P.coroot j)) =
          facetDerivativeRootCorootGraph B T D hT F

end RelativeComponentModelHom
end Facet
end Langlands.BruhatTits.IntegralModels
