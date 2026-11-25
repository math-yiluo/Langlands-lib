/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorBase
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensor

/-! # Evaluation and scalar tensor comparisons for semilinear systems

## References

* Zheng, Construction 4.1
* Stacks Project, Tags 06YY and 07A4
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
variable (S : SystemScalarCoherence.{c, v, r} J B τ)
/-- Comparisons between the base tensor models and their evaluations/scalar extensions. -/
structure SystemTensorComparisons (A : SystemTensorBase.{c, v, r} J B τ) where
  tensorEvaluation : ∀ n : ℕ,
    A.closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
      ((e.{c, v, max c v r} J B τ n).prod
        (e.{c, v, max c v r} J B τ n)) ⋙ (A.levelClosed n).tensor
  tensorEvaluationModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r}
      (coefficientSequenceTopology J) J
      (systemRing.{c, v, max c v r} J B τ) (B n)
      (evaluation.{c, v, max c v r} J B τ n)
      A.closed (A.levelClosed n) A.tensorModels (A.levelTensorModels n)
      (tensorEvaluation n)
  tensorEvaluationModel_ordinary : ∀ (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ),
    (tensorEvaluationModel n).ordinary M N =
      ordinaryEvaluationTensor.{c, v, r} J B τ n M N
  scalarTensor : ∀ {m n : ℕ} (h : n ≤ m),
    (A.levelClosed m).tensor ⋙ (S.scalar h).T ≅
      ((S.scalar h).T.prod (S.scalar h).T) ⋙ (A.levelClosed n).tensor
  scalarTensorModel : ∀ {m n : ℕ} (h : n ≤ m),
    ScalarTensorComparisonModel.{c, v, r} J (B m) (B n)
      (coefficientMap.{c, v, max c v r} J B τ h) (S.scalar h)
      (A.levelClosed m) (A.levelClosed n)
      (A.levelTensorModels m) (A.levelTensorModels n) (scalarTensor h)
/-- The comparisons between the base tensor models and their evaluations and scalar extensions
exist. -/
theorem systemTensorComparisons_nonempty (A : SystemTensorBase.{c, v, r} J B τ) :
    Nonempty (SystemTensorComparisons.{c, v, r} J B τ S A) := by
  classical
  have he := fun n : ℕ ↦ semilinearTensorEvaluation.{c, v, r} J B τ n
    A.closed A.tensorModels (A.levelClosed n) (A.levelTensorModels n)
  have hs := fun (m n : ℕ) (h : n ≤ m) ↦ semilinearScalarTensor.{c, v, r} J
    (B m) (B n) (coefficientMap.{c, v, max c v r} J B τ h) (S.scalar h)
    (A.levelClosed m) (A.levelClosed n) (A.levelTensorModels m) (A.levelTensorModels n)
  exact ⟨{
    tensorEvaluation := fun n ↦ (he n).choose
    tensorEvaluationModel := fun n ↦ (he n).choose_spec.choose
    tensorEvaluationModel_ordinary := fun n ↦ (he n).choose_spec.choose_spec
    scalarTensor := fun {m n} h ↦ (hs m n h).choose
    scalarTensorModel := fun {m n} h ↦ (hs m n h).choose_spec.some
  }⟩
end WeilConjectures.SemilinearSections
