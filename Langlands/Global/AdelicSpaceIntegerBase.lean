import Langlands.Global.NumberFieldPrincipalSIntegerFiniteType
import Langlands.Global.CurvePlacePrincipalSIntegerFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Integer bases for cofinal actual adelic models -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

noncomputable section

namespace Langlands.Global.AdelicSpaceIntegerBase

/-- Every commutative ring has its canonical algebra structure over the universe-lifted integers. -/
@[instance_reducible]
def algebra (C : Type u) [CommRing C] : Algebra (ULift.{u} ℤ) C :=
  ULift.algebra' ℤ C

/-- Finite type over the original integers gives local finite type over their universe lift,
for every algebra structure over the lifted integers. -/
theorem locallyOfFiniteType (C : Type u) [CommRing C] [Algebra (ULift.{u} ℤ) C]
    [Algebra.FiniteType ℤ C] : LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) C) := by
  let := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ULift.{u} ℤ) (A := C)
    (Subsingleton.elim _ _)
  have : Algebra.FiniteType (ULift.{u} ℤ) C :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ULift.{u} ℤ) C
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) C)))
  apply HasRingHomProperty.Spec_iff.mpr
  exact (RingHom.finiteType_algebraMap).mpr inferInstance

/-- Every finite initial set of number-field places has an actual cofinal integer level
whose canonical integer-base map is locally of finite type. -/
theorem numberField_cofinal (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)) :
    letI := algebra ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K)
    LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ)
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K)) := by
  let := algebra ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
    Set (FinitePlace K)).integer K)
  exact locallyOfFiniteType _

/-- Every finite initial set of curve places has an actual cofinal integer level
whose canonical integer-base map is locally of finite type. -/
theorem curvePlace_cofinal (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)) :
    letI := algebra (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
    LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ)
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)) := by
  let := algebra (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
  exact locallyOfFiniteType _

end Langlands.Global.AdelicSpaceIntegerBase
