import Langlands.ClassFieldTheory.Local.ClosureRestrictionTransport
import Langlands.Cohomology.Continuous.FiniteQuotientSystem

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K]
variable (E : IntermediateField K (AlgebraicClosure K))
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

/-- The supplied closure equivalence on the actual unit modules. -/
def closureUnitLinearEquiv : absoluteUnits K ≃ₗ[IntegerScalars.{u}] absoluteUnits E :=
  (Units.mapEquiv (suppliedClosureEquiv K E).toMulEquiv).toAdditive.toIntLinearEquiv.restrictScalars
    IntegerScalars.{u}

/-- Discrete topology makes the coefficient equivalence continuous in both directions. -/
def closureUnitContinuousEquiv : absoluteUnits K ≃L[IntegerScalars.{u}] absoluteUnits E :=
  { closureUnitLinearEquiv K E with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- Its forward map is exactly the existing absolute-restriction coefficient map. -/
theorem closureUnitLinearEquiv_apply (x : absoluteUnits K) :
    closureUnitLinearEquiv K E x = absoluteRestrictionCoefficients K E x := rfl

/-- The inverse coefficient map, equivariant for the actual absolute Galois map. -/
def absoluteRestrictionCoefficientsInverse :
    absoluteUnits E ⟶ TopRep.res (Field.absoluteGaloisGroup.mapOfAlgebra K E) (absoluteUnits K) where
  hom' :=
    { toContinuousLinearMap := (closureUnitContinuousEquiv K E).symm.toContinuousLinearMap
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply (closureUnitLinearEquiv K E).injective
        change closureUnitLinearEquiv K E
          ((closureUnitLinearEquiv K E).symm ((absoluteUnits E).ρ σ x)) =
            closureUnitLinearEquiv K E
              ((absoluteUnits K).ρ (Field.absoluteGaloisGroup.mapOfAlgebra K E σ)
                ((closureUnitLinearEquiv K E).symm x))
        rw [LinearEquiv.apply_symm_apply]
        have h := TopRep.hom_comm_apply (absoluteRestrictionCoefficients K E) σ
          ((closureUnitLinearEquiv K E).symm x)
        change closureUnitLinearEquiv K E
          ((absoluteUnits K).ρ (Field.absoluteGaloisGroup.mapOfAlgebra K E σ)
            ((closureUnitLinearEquiv K E).symm x)) =
              (absoluteUnits E).ρ σ
                (closureUnitLinearEquiv K E ((closureUnitLinearEquiv K E).symm x)) at h
        rw [LinearEquiv.apply_symm_apply] at h
        exact h.symm }

/-- Absolute restriction has an intrinsic coefficient isomorphism for the supplied embedding. -/
def absoluteRestrictionCoefficientsIso :
    TopRep.res (Field.absoluteGaloisGroup.mapOfAlgebra K E) (absoluteUnits K) ≅ absoluteUnits E where
  hom := absoluteRestrictionCoefficients K E
  inv := absoluteRestrictionCoefficientsInverse K E
  hom_inv_id := by
    ext x
    exact (closureUnitLinearEquiv K E).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (closureUnitLinearEquiv K E).apply_symm_apply x

@[simp] theorem absoluteRestrictionCoefficientsIso_hom :
    (absoluteRestrictionCoefficientsIso K E).hom = absoluteRestrictionCoefficients K E := rfl

variable [Normal K E] [CharZero K]

set_option backward.isDefEq.respectTransparency false in
/-- The same coefficient isomorphism after restriction to the actual fixing subgroup. -/
def closureSubgroupCoefficientsIso :
    TopRep.res (closureSubgroupEquiv K E).toMonoidHom
      (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K)) ≅
        absoluteUnits E :=
  absoluteRestrictionCoefficientsIso K E

set_option backward.isDefEq.respectTransparency false in
/-- The continuous inclusion after group transport is the actual absolute Galois map. -/
theorem closureSubgroupEquiv_comp_inclusion :
    (Langlands.Continuous.subgroupInclusion (G := Field.absoluteGaloisGroup K) E.fixingSubgroup).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (closureSubgroupEquiv K E)) =
        Field.absoluteGaloisGroup.mapOfAlgebra K E := rfl

end Langlands.ClassFieldTheory.Local
