import Langlands.Global.NumberFieldSIntegerLocalTensor
import Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor

noncomputable section

universe u

open IsDedekindDomain IntermediateField AlgebraicCurve
open scoped NumberField TensorProduct AlgebraicCurve.CurveModel
  IntermediateField.algebraAdjoinAdjoin Langlands.Global
  Langlands.Global.NumberFieldSIntegers Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  NumberField.LiesOver Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension

namespace Langlands.Global

private def coefficientBaseChangeEquiv (A B K L C : Type u)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L] [CommRing C]
    [Algebra A B] [Algebra A K] [Algebra A C] [Algebra K L] [Algebra K C]
    [IsScalarTower A K C] (e : K ⊗[A] B ≃ₐ[K] L) :
    C ⊗[A] B ≃ₐ[C] (C ⊗[K] L) :=
  (Algebra.TensorProduct.cancelBaseChange A K C C B).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := C) (A₁ := C)) e)

private theorem coefficientBaseChangeEquiv_tmul (A B K L C : Type u)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L] [CommRing C]
    [Algebra A B] [Algebra A K] [Algebra A C] [Algebra K L] [Algebra K C]
    [IsScalarTower A K C] (e : K ⊗[A] B ≃ₐ[K] L) (a : C) (b : B) :
    coefficientBaseChangeEquiv A B K L C e (a ⊗ₜ[A] b) =
      a ⊗ₜ[K] e (1 ⊗ₜ[A] b) := by
  simp only [coefficientBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

namespace NumberFieldSIntegerFieldTensor

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (p : FinitePlace K)

/-- The actual S-integer coefficients tensored with any original lower completed field. -/
def tensorEquiv :
    p.adicCompletion K ⊗[(S : Set (FinitePlace K)).integer K]
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) ≃ₐ[p.adicCompletion K]
      (∀ q : AdelicFunctoriality.FinitePlacesAbove L p, q.1.adicCompletion L) :=
  (coefficientBaseChangeEquiv ((S : Set (FinitePlace K)).integer K) _ K L
    (p.adicCompletion K) (numberFieldSIntegersFractionTensorEquiv K L S)).trans
      (AlgEquiv.ofBijective (AdelicFunctoriality.finiteTensorMap p)
        ((AdelicFunctoriality.completedTensorComparison K L).1 p))

@[simp]
theorem tensorEquiv_tmul (a : p.adicCompletion K)
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    tensorEquiv K L S p (a ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      AdelicFunctoriality.FiniteExtension.completionMap p q.1 a *
        algebraMap L (q.1.adicCompletion L) (b : L) := by
  simp only [tensorEquiv, AlgEquiv.trans_apply, coefficientBaseChangeEquiv_tmul,
    numberFieldSIntegersFractionTensorEquiv_tmul, map_one, one_mul]
  rfl

@[simp]
theorem tensorEquiv_one_tmul
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    tensorEquiv K L S p (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      algebraMap
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) (q.1.adicCompletion L) b := by
  simp only [tensorEquiv_tmul, map_one, one_mul]
  rfl

scoped instance integralToFieldTower [Fact (p ∉ S)] :
    IsScalarTower ((S : Set (FinitePlace K)).integer K)
      (p.adicCompletionIntegers K) (p.adicCompletion K) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance upperIntegralToFieldTower [Fact (p ∉ S)]
    (q : AdelicFunctoriality.FinitePlacesAbove L p) :
    IsScalarTower
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L)
      (q.1.adicCompletionIntegers L) (q.1.adicCompletion L) :=
  .of_algebraMap_eq fun _ => rfl

end NumberFieldSIntegerFieldTensor

namespace NumberFieldSIntegerInfiniteTensor

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (p : NumberField.InfinitePlace K)

/-- The actual S-integer coefficients at an original infinite lower place. -/
def tensorEquiv :
    p.Completion ⊗[(S : Set (FinitePlace K)).integer K]
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) ≃ₐ[p.Completion]
      (∀ q : AdelicFunctoriality.InfinitePlacesAbove L p, q.1.Completion) :=
  (coefficientBaseChangeEquiv ((S : Set (FinitePlace K)).integer K) _ K L
    p.Completion (numberFieldSIntegersFractionTensorEquiv K L S)).trans
      (AdelicFunctoriality.infiniteTensorEquiv p)

@[simp]
theorem tensorEquiv_tmul (a : p.Completion)
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.InfinitePlacesAbove L p) :
    tensorEquiv K L S p (a ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      NumberField.LiesOver.completionMap a * algebraMap L q.1.Completion (b : L) := by
  simp only [tensorEquiv, AlgEquiv.trans_apply, coefficientBaseChangeEquiv_tmul,
    numberFieldSIntegersFractionTensorEquiv_tmul, map_one, one_mul]
  rfl

@[simp]
theorem tensorEquiv_one_tmul
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : AdelicFunctoriality.InfinitePlacesAbove L p) :
    tensorEquiv K L S p (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      algebraMap
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) q.1.Completion b := by
  simp only [tensorEquiv_tmul, map_one, one_mul]
  rfl

end NumberFieldSIntegerInfiniteTensor

namespace CurvePlacePrincipalSIntegerFieldTensor

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)] (p : Place k K)

/-- The actual principal S-integer coefficients at every original completed lower field. -/
def tensorEquiv :
    curvePlaceCompletion p ⊗[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[curvePlaceCompletion p]
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
  (coefficientBaseChangeEquiv
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ K L
    (curvePlaceCompletion p) (curvePlacePrincipalSIntegersFractionTensorEquiv k K L s t)).trans
      (CurvePlaceCompletedTensorEquiv.allTensorEquiv p)

@[simp]
theorem tensorEquiv_tmul (a : curvePlaceCompletion p)
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : CurvePlacesAbove k L p) :
    tensorEquiv k K L s t p
      (a ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := by
  simp only [tensorEquiv, AlgEquiv.trans_apply, coefficientBaseChangeEquiv_tmul,
    curvePlacePrincipalSIntegersFractionTensorEquiv_tmul, map_one, one_mul]
  rfl

@[simp]
theorem tensorEquiv_one_tmul
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : CurvePlacesAbove k L p) :
    tensorEquiv k K L s t p
      (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
      algebraMap
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion q.1) b := by
  simp only [tensorEquiv_tmul, map_one, one_mul]
  rfl

scoped instance integralToFieldTower
    [Fact (p ∉ curvePlacePrincipalExceptional k K s (t : K))] :
    IsScalarTower
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (curvePlaceCompletionIntegers p) (curvePlaceCompletion p) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance upperIntegralToFieldTower
    [Fact (p ∉ curvePlacePrincipalExceptional k K s (t : K))] (q : CurvePlacesAbove k L p) :
    IsScalarTower
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))
      (curvePlaceCompletionIntegers q.1) (curvePlaceCompletion q.1) :=
  .of_algebraMap_eq fun _ => rfl

end CurvePlacePrincipalSIntegerFieldTensor

end Langlands.Global
