import Langlands.BruhatTits.IntegralModels.FacetLieWeights

/-! # Character restriction and specialization through integral split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G G' : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {D' : RelativeComponentModelData R K G'}
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G'}
  (T : IntegralTorusData D S i) (T' : IntegralTorusData D' S' i')

/-- The actual generic-fibre homomorphism, expressed on the two specified
generic tori using their supplied generic identifications. -/
def genericFibreMap (ρ : T.torus ⟶ T'.torus) : S ⟶ S' :=
  (CommGroupScheme.isoOfGroupIso T.genericIso).inv ≫
    (CommGroupScheme.baseChange (Spec.algebraMap R K)).map ρ ≫
      (CommGroupScheme.isoOfGroupIso T'.genericIso).hom

variable {T T'}

omit [IsLocalRing R] in
/-- The generic character of a restricted integral character is the
restriction of its generic character along the actual generic map. -/
theorem genericCharacter_comp (ρ : T.torus ⟶ T'.torus)
    (ψ : characterLattice T'.torus) :
    T.genericCharacter (ρ ≫ ψ) =
      T.genericFibreMap T' ρ ≫ T'.genericCharacter ψ := by
  change (CommGroupScheme.isoOfGroupIso T.genericIso).inv ≫
      characterLattice.baseChange (Spec.algebraMap R K) T.torus (ρ ≫ ψ) =
    ((CommGroupScheme.isoOfGroupIso T.genericIso).inv ≫
      (CommGroupScheme.baseChange (Spec.algebraMap R K)).map ρ ≫
      (CommGroupScheme.isoOfGroupIso T'.genericIso).hom) ≫
    ((CommGroupScheme.isoOfGroupIso T'.genericIso).inv ≫
      characterLattice.baseChange (Spec.algebraMap R K) T'.torus ψ)
  rw [characterLattice.baseChange_precomp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Canonical generic-to-special character specialization commutes with
restriction along the supplied integral torus morphism. -/
theorem characterSpecialization_comp
    (hT : IsSplitTorus T.torus.toGrp) (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : T.torus ⟶ T'.torus) (χ : characterLattice S') :
    T.characterSpecialization hT (T.genericFibreMap T' ρ ≫ χ) =
      (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ ≫
        T'.characterSpecialization hT' χ := by
  obtain ⟨ψ, hψ⟩ := (T'.genericCharacterEquiv hT').surjective χ
  change T'.genericCharacter ψ = χ at hψ
  rw [← hψ, ← genericCharacter_comp,
    characterSpecialization_genericCharacter, characterSpecialization_genericCharacter]
  exact characterLattice.baseChange_precomp _ ρ ψ

/-- A generic character restricts to zero exactly when its canonical
specialization restricts to zero on the residue torus. -/
theorem generic_restriction_eq_zero_iff
    (hT : IsSplitTorus T.torus.toGrp) (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : T.torus ⟶ T'.torus) (χ : characterLattice S') :
    T.genericFibreMap T' ρ ≫ χ = 0 ↔
      (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ ≫
        T'.characterSpecialization hT' χ = 0 := by
  rw [← characterSpecialization_comp hT hT' ρ χ]
  exact (T.characterSpecialization hT).map_eq_zero_iff.symm

/-- Nonzero restriction on the residue torus is equivalent to nonzero
restriction on the specified generic torus. -/
theorem generic_restriction_ne_zero_iff
    (hT : IsSplitTorus T.torus.toGrp) (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : T.torus ⟶ T'.torus) (χ : characterLattice S') :
    T.genericFibreMap T' ρ ≫ χ ≠ 0 ↔
      (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ρ ≫
        T'.characterSpecialization hT' χ ≠ 0 :=
  not_congr (generic_restriction_eq_zero_iff hT hT' ρ χ)

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
