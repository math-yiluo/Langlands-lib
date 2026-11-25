/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence

/-! # Normalized coefficient extension on semilinear systems

## References

* Zheng Construction 4.1 and Lemma 4.10
* Stacks 06YY, 07A4, 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Normalized coefficient extension on semilinear systems. -/
theorem semilinearScalarOperations
    (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n) :
    Nonempty (ScalarSystems.{c, v, r} J B τ F σ α hα) := by
  classical
  obtain ⟨hS, hL⟩ := semilinearScalarData.{c, v, r} J B τ F σ α hα
  let S := hS.some
  let L : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α n) := fun n ↦ (hL n).some
  obtain ⟨E⟩ :=
    semilinearScalarEvaluationTranspose.{c, v, r} J B τ F σ α hα S L
  exact ⟨{
    scalar := S
    levels := L
    evaluation := E.evaluation
    transpose_evaluation := E.transpose_evaluation }⟩

end WeilConjectures.SemilinearSections
