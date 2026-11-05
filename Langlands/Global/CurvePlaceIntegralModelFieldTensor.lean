import Langlands.Global.CurvePlaceIntegralTensor

/-! # Completed-field tensor of the original function-field integral model coefficients -/

noncomputable section

universe u

open scoped TensorProduct Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor

namespace Langlands.Global.CurvePlaceIntegralModelFieldTensor

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  (p : AlgebraicCurve.Place k K)

scoped instance (priority := 50) (q : CurvePlacesAbove k L p) :
    Algebra p.toValuationSubring (curvePlaceCompletion q.1) :=
  ((algebraMap L (curvePlaceCompletion q.1)).comp (algebraMap p.toValuationSubring L)).toAlgebra

scoped instance (priority := 50) (q : CurvePlacesAbove k L p) :
    Algebra (curvePlaceIntegralClosure L p) (curvePlaceCompletion q.1) :=
  ((algebraMap L (curvePlaceCompletion q.1)).comp
    (algebraMap (curvePlaceIntegralClosure L p) L)).toAlgebra

scoped instance (q : CurvePlacesAbove k L p) :
    IsScalarTower p.toValuationSubring (curvePlaceIntegralClosure L p)
      (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance (q : CurvePlacesAbove k L p) :
    IsScalarTower (curvePlaceIntegralClosure L p) (curvePlaceCompletionIntegers q.1)
      (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance (q : CurvePlacesAbove k L p) :
    IsScalarTower p.toValuationSubring (curvePlaceCompletion p) (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun r => by
    change algebraMap L (curvePlaceCompletion q.1) (algebraMap K L (r : K)) =
      CurvePlaceCompletionExtension.completionMap p q
        (algebraMap K (curvePlaceCompletion p) (r : K))
    exact (CurvePlaceCompletionExtension.completionMap_algebraMap p q (r : K)).symm

/-- The original integral closure, tensored with the original lower completed field. -/
def tensorMap :
    curvePlaceCompletion p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p →ₐ[
      curvePlaceCompletion p] (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
  AlgHom.pi fun q => Algebra.TensorProduct.lift
    (Algebra.ofId (curvePlaceCompletion p) (curvePlaceCompletion q.1))
    (Algebra.algHom p.toValuationSubring (curvePlaceIntegralClosure L p)
      (curvePlaceCompletion q.1)) (fun _ _ => .all _ _)

@[simp]
theorem tensorMap_tmul (a : curvePlaceCompletion p) (b : curvePlaceIntegralClosure L p)
    (q : CurvePlacesAbove k L p) :
    tensorMap (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

variable [FiniteDimensional K L] [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [IsScalarTower k K L]

/-- This is the already proved original localization-and-field comparison. -/
theorem tensorMap_eq_fieldComparison :
    (tensorMap (L := L) p : _ → _) = CurvePlaceIntegralTensor.fieldComparison (L := L) p := by
  funext z
  induction z with
  | tmul a b =>
    funext q
    rw [tensorMap_tmul, CurvePlaceIntegralTensor.fieldComparison_tmul]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The actual field tensor equivalence keeps the original valuation-ring model coefficients. -/
def tensorEquiv :
    curvePlaceCompletion p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p ≃ₐ[
      curvePlaceCompletion p] (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
  AlgEquiv.ofBijective (tensorMap p) (by
    rw [tensorMap_eq_fieldComparison]
    exact (CurvePlaceIntegralTensor.fieldComparison (L := L) p).bijective)

@[simp]
theorem tensorEquiv_tmul (a : curvePlaceCompletion p) (b : curvePlaceIntegralClosure L p)
    (q : CurvePlacesAbove k L p) :
    tensorEquiv (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

@[simp]
theorem tensorEquiv_one_tmul (b : curvePlaceIntegralClosure L p) (q : CurvePlacesAbove k L p) :
    tensorEquiv (L := L) p (1 ⊗ₜ[p.toValuationSubring] b) q =
      algebraMap (curvePlaceIntegralClosure L p) (curvePlaceCompletion q.1) b := by
  simp only [tensorEquiv_tmul, map_one, one_mul]
  rfl

end Langlands.Global.CurvePlaceIntegralModelFieldTensor
