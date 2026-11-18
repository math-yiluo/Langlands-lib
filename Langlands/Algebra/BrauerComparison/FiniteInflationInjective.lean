import Langlands.Algebra.BrauerComparison.SeparableFiniteStages
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof

/-! # Injectivity of finite-stage inflation on continuous degree-two unit cohomology -/

noncomputable section

open CategoryTheory Langlands.Continuous

universe u

namespace Langlands.BrauerComparison

open ClassFieldTheory.Local

variable (K S : Type u) [Field K] [Field S] [Algebra K S] [IsGalois K S]

set_option backward.isDefEq.respectTransparency false in
/-- Degree-two relative inflation from an open normal fixed field is injective. -/
theorem relativeToContinuous_fixedStage_injective (N : OpenNormalSubgroup Gal(S/K)) :
    Function.Injective (relativeToContinuous K (galoisFixedStage K S N) S 2) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := (galoisFixedStageIso K S N 2).toLinearEquiv.surjective x
  have hy : finiteStageToContinuous (galoisUnitModule K S) N 2 y = 0 :=
    (finiteStageToContinuous_eq_relativeToContinuous K S N 2 y).trans hx
  obtain ⟨P, hPN, hz⟩ := finiteStageToContinuous_eventually_zero (galoisUnitModule K S) N 2 y hy
  let E := IntermediateField.fixedField N.toSubgroup
  let F := IntermediateField.fixedField P.toSubgroup
  let : Algebra E F := FixedFieldRefinement.inclusionAlgebra hPN
  have : IsScalarTower K E F := FixedFieldRefinement.baseTower hPN
  have : FiniteDimensional K E := (galoisFixedStage K S N).finiteDimensional
  have : FiniteDimensional K F := (galoisFixedStage K S P).finiteDimensional
  have : IsGalois K E := (galoisFixedStage K S N).isGalois
  have : IsGalois K F := (galoisFixedStage K S P).isGalois
  have hcomp := ConcreteCategory.congr_hom (FixedFieldRefinement.cohomology_inflation hPN 2) y
  apply (finiteRelativeH2InflationExactness K E F).1
  rw [map_zero]
  change relativeInflation K E F 2 ((galoisFixedStageIso K S N 2).hom y) = 0
  refine hcomp.symm.trans ?_
  change (galoisFixedStageIso K S P 2).hom
    (finiteInflation (galoisUnitModule K S).toRep 2 hPN y) = 0
  rw [hz, map_zero]

/-- The open normal subgroup fixing a finite Galois intermediate field. -/
def finiteStageFixingSubgroup (E : FiniteGaloisIntermediateField K S) :
    OpenNormalSubgroup Gal(S/K) where
  toSubgroup := E.toIntermediateField.fixingSubgroup
  isOpen' := E.toIntermediateField.fixingSubgroup_isOpen
  isNormal' := IsGalois.fixingSubgroup_normal_of_isGalois E.toIntermediateField

private theorem relativeToContinuous_injective_of_fixedStage (E : IntermediateField K S)
    [FiniteDimensional K E] [IsGalois K E] (N : OpenNormalSubgroup Gal(S/K))
    (hE : (galoisFixedStage K S N).toIntermediateField = E) :
    Function.Injective (relativeToContinuous K E S 2) := by
  subst E
  exact relativeToContinuous_fixedStage_injective K S N

/-- Inflation from any actual finite Galois intermediate field is injective
in continuous degree-two unit cohomology. -/
theorem relativeToContinuous_injective (E : FiniteGaloisIntermediateField K S) :
    Function.Injective (relativeToContinuous K E S 2) :=
  relativeToContinuous_injective_of_fixedStage K S E.toIntermediateField
    (finiteStageFixingSubgroup K S E)
    (InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField)

end Langlands.BrauerComparison
