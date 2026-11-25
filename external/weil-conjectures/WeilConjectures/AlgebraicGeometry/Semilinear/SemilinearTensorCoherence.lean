/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorBase
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorReduction

/-! # Tensor coherence for derived systems

## References

* Zheng, Construction 4.1 and Proposition 4.17
* Stacks Tags 06YY, 07A4, 07A6 and 08J9
* Zheng Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

variable (S : SystemScalarCoherence.{c, v, r} J B τ)

/-- Tensor constructions and comparison models, including reduction compatibility. -/
structure SystemTensorCoherence where
  /-- System tensor is covariant in both variables and closed against the recorded Hom. -/
  closed : Closed.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
  /-- Its actual K-flat total-complex model. -/
  tensorModels : Models.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) closed
  /-- Retain the normalized unit, associator and symmetry of this same closed structure. -/
  tensorNormalization : Nonempty { M : NormalizedTensorModel.{c, v, r}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) //
      M.closed = closed }
  /-- The same closed structure at each actual coefficient level. -/
  levelClosed : ∀ n : ℕ, Closed.{c, v, r} J (B n)
  /-- The levelwise total tensor models. -/
  levelTensorModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (levelClosed n)
  /-- The natural tensor evaluation isomorphism. -/
  tensorEvaluation : ∀ n : ℕ,
    closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
      ((e.{c, v, max c v r} J B τ n).prod (e.{c, v, max c v r} J B τ n)) ⋙ (levelClosed n).tensor
  /-- The evaluation comparison is the localized tensor comparison model, with
  its ordinary map fixed by the sectionwise pure-tensor comparison below. -/
  tensorEvaluationModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r}
      (coefficientSequenceTopology J) J
      (systemRing.{c, v, max c v r} J B τ) (B n)
      (evaluation.{c, v, max c v r} J B τ n)
      closed (levelClosed n) tensorModels (levelTensorModels n)
      (tensorEvaluation n)
  /-- The ordinary component of the evaluation model is exactly the
  identity-on-sections comparison, so it cannot be sign-twisted. -/
  tensorEvaluationModel_ordinary : ∀ (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ),
    (tensorEvaluationModel n).ordinary M N =
      ordinaryEvaluationTensor.{c, v, r} J B τ n M N
  /-- Tensor commutes with the actual derived coefficient extension. -/
  scalarTensor : ∀ {m n : ℕ} (h : n ≤ m),
    (levelClosed m).tensor ⋙ (S.scalar h).T ≅
      ((S.scalar h).T.prod (S.scalar h).T) ⋙ (levelClosed n).tensor
  /-- Scalar/tensor comparison on K-flat representatives.  Its counit square
  uses the actual derived change-of-rings model, and its ordinary comparison is
  fixed on pure tensors. -/
  scalarTensorModel : ∀ {m n : ℕ} (h : n ≤ m),
    ScalarTensorComparisonModel.{c, v, r} J (B m) (B n)
      (coefficientMap.{c, v, max c v r} J B τ h) (S.scalar h)
      (levelClosed m) (levelClosed n)
      (levelTensorModels m) (levelTensorModels n) (scalarTensor h)
  /-- Reducing the tensor is the tensor of the two reductions. -/
  reduction_tensor : ∀ {m n : ℕ} (h : n ≤ m)
    (M N : DS.{c, v, max c v r} J B τ),
    (S.scalar h).T.map ((tensorEvaluation m).hom.app (M, N)) ≫
        (scalarTensor h).hom.app
          ((e.{c, v, max c v r} J B τ m).obj M,
            (e.{c, v, max c v r} J B τ m).obj N) ≫
        (levelClosed n).tensor.map
          (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (S.scalar h) M)
            (reduction.{c, v, max c v r} J B τ h (S.scalar h) N)) =
      reduction.{c, v, max c v r} J B τ h (S.scalar h) (closed.tensor.obj (M, N)) ≫
        (tensorEvaluation n).hom.app (M, N)

/-- Representative-normalized tensor structures on the sequence site and its levels. -/
theorem systemTensorCoherence_nonempty :
    Nonempty (SystemTensorCoherence.{c, v, r} J B τ S) := by
  obtain ⟨A⟩ := systemTensorBase_nonempty.{c, v, r} J B τ
  obtain ⟨T⟩ := systemTensorComparisons_nonempty.{c, v, r} J B τ S A
  exact ⟨{
    closed := A.closed
    tensorModels := A.tensorModels
    tensorNormalization := A.tensorNormalization
    levelClosed := A.levelClosed
    levelTensorModels := A.levelTensorModels
    tensorEvaluation := T.tensorEvaluation
    tensorEvaluationModel := T.tensorEvaluationModel
    tensorEvaluationModel_ordinary := T.tensorEvaluationModel_ordinary
    scalarTensor := T.scalarTensor
    scalarTensorModel := T.scalarTensorModel
    reduction_tensor := by
      intro m n h M N
      exact systemTensorReduction.{c, v, r} J B τ S A T h M N }⟩

end WeilConjectures.SemilinearSections
