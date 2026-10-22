import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.ClassFieldTheory.Local.FiniteComparison
import Langlands.Cohomology.Continuous.FiniteStageFactorization

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K] [CharZero K]
variable (E : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K E] [IsGalois K E]

/-- The intrinsic cochain identification for the fixing subgroup of a finite Galois field. -/
def finiteGaloisStageCochainIso :
    groupCohomology.inhomogeneousCochains
      (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
        (finiteGaloisFixingSubgroup K E)) ≅
      groupCohomology.inhomogeneousCochains (unitsRepresentation K E) :=
  finiteStageCochainIso (absoluteUnitDiscreteModule K) (finiteGaloisFixingSubgroup K E)
    (discreteUnitsRepresentation K E) (finiteGaloisStageGroupEquiv K E)
    (finiteGaloisStageUnitsLinearEquiv K E)
    (finiteGaloisStageUnitsLinearEquiv_intertwines K E)

/-- Its homology map is the direct identification with the specified field's relative cohomology. -/
theorem finiteGaloisStageCochainIso_homologyMap (q : ℕ) :
    HomologicalComplex.homologyMap (finiteGaloisStageCochainIso K E).hom q =
      (finiteGaloisStageRelativeIso K E q).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The finite stage map is the existing closure inflation under the intrinsic identification. -/
theorem finiteGaloisStageRelativeIso_closureInflation (q : ℕ)
    (x : groupCohomology (finiteQuotientRep (absoluteUnitDiscreteModule K).toRep
      (finiteGaloisFixingSubgroup K E)) q) :
    finiteStageToContinuous (absoluteUnitDiscreteModule K)
      (finiteGaloisFixingSubgroup K E) q x =
      closureInflation K E q ((finiteGaloisStageRelativeIso K E q).hom x) := by
  have h := finiteStageToContinuous_eq_mapIso (absoluteUnitDiscreteModule K)
    (finiteGaloisFixingSubgroup K E) (discreteUnitsRepresentation K E)
    (finiteGaloisStageGroupEquiv K E) (finiteGaloisStageUnitsLinearEquiv K E)
    (finiteGaloisStageUnitsLinearEquiv_intertwines K E)
    (closureRestriction K E) (closureInflationCoefficients K E)
    (finiteGaloisStageGroupEquiv_mk K E)
    (finiteGaloisStageUnitsLinearEquiv_inclusion K E) q
  exact congrArg (fun f => f x) h

end Langlands.ClassFieldTheory.Local
