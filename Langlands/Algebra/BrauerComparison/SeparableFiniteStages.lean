import Langlands.Algebra.BrauerComparison.SeparableCohomology
import Langlands.ClassFieldTheory.Local.FixedFieldStageInflation
import Langlands.Cohomology.Continuous.FiniteStageFactorization
import Langlands.Cohomology.Continuous.FiniteStageExactnessLimitProof

/-! # Actual finite Galois stages of continuous unit cohomology -/

noncomputable section

open CategoryTheory Langlands.Continuous

universe u

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local

variable (K S : Type u) [Field K] [Field S] [Algebra K S] [IsGalois K S]

/-- The finite Galois intermediate field fixed by an open normal subgroup. -/
def galoisFixedStage (N : OpenNormalSubgroup Gal(S/K)) : FiniteGaloisIntermediateField K S where
  toIntermediateField := IntermediateField.fixedField N.toSubgroup
  finiteDimensional := by
    apply (InfiniteGalois.isOpen_iff_finite _).mp
    change IsOpen (IntermediateField.fixedField (FixedFieldRefinement.closed K S N).toSubgroup
      ).fixingSubgroup.carrier
    rw [InfiniteGalois.fixingSubgroup_fixedField]
    exact N.toOpenSubgroup.isOpen
  isGalois := IsGalois.of_fixedField_normal_subgroup N.toSubgroup

/-- The quotient-group and fixed-unit identifications for an actual finite Galois stage. -/
abbrev galoisFixedStageIso (N : OpenNormalSubgroup Gal(S/K)) (q : ℕ) :
    groupCohomology (finiteQuotientRep (galoisUnitModule K S).toRep N) q ≅
      relativeCohomology K (galoisFixedStage K S N) q :=
  fixedFieldCohomologyIso K S (FixedFieldRefinement.closed K S N) q

set_option backward.isDefEq.respectTransparency false in
/-- The finite-quotient comparison is inflation from the ordinary cohomology
of the actual finite Galois fixed field. -/
theorem finiteStageToContinuous_eq_relativeToContinuous
    (N : OpenNormalSubgroup Gal(S/K)) (q : ℕ)
    (x : groupCohomology (finiteQuotientRep (galoisUnitModule K S).toRep N) q) :
    finiteStageToContinuous (galoisUnitModule K S) N q x =
      relativeToContinuous K (galoisFixedStage K S N) S q
        ((galoisFixedStageIso K S N q).hom x) := by
  let E := galoisFixedStage K S N
  let H := FixedFieldRefinement.closed K S N
  have h := finiteStageToContinuous_eq_mapIso (galoisUnitModule K S) N
    (discreteUnitsRepresentation K E) (InfiniteGalois.normalAutEquivQuotient H)
    (fixedFieldUnitsLinearEquiv K S H.toSubgroup)
    (fixedFieldUnitsLinearEquiv_intertwines K S H)
    (normalKrullRestriction K E S) (continuousUnitInflationCoefficients K E S)
    (fun _ => rfl) (fun _ => by apply Units.ext; rfl) q
  exact ConcreteCategory.congr_hom h x

/-- Every continuous unit cohomology class comes from an actual finite Galois extension. -/
theorem exists_finiteRelativeToContinuous (q : ℕ) (x : continuousUnitCohomology K S q) :
    ∃ (E : FiniteGaloisIntermediateField K S) (y : relativeCohomology K E q),
      relativeToContinuous K E S q y = x := by
  obtain ⟨N, y, hy⟩ := finiteStageToContinuous_jointly_surjective (galoisUnitModule K S) q x
  refine ⟨galoisFixedStage K S N, (galoisFixedStageIso K S N q).hom y, ?_⟩
  exact (finiteStageToContinuous_eq_relativeToContinuous K S N q y).symm.trans hy

end Langlands.BrauerComparison
