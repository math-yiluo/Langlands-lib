/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarModel

/-! # Existence of normalized scalar data

## References

* Zheng, Construction 4.1 and Lemma 4.10
* Stacks 06YY and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
universe c v r

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.SemilinearSections

private theorem scalarData_nonempty
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S) :
    Nonempty (ScalarData.{c, v, max c v r} φ) := by
  obtain ⟨A⟩ := SheafOfModules.nonempty_systemScalarModel φ
  refine ⟨{ model := A.model
            ordinaryAdjunction := A.ordinaryAdj
            unit_section := ?_
            adjunction := A.adjunction
            transpose_model := ?_ }⟩
  · intro M U x
    rw [A.unit_normalized]
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    have hh : eqToHom (A.model.obj_eq M).symm ≫ eqToHom (A.model.obj_eq M) =
        𝟙 _ := by simp
    exact congrArg (fun f ↦ f.val.app U (extensionUnit.{c, v, max c v r} φ M U x)) hh
  · intro P Q _ f
    rw [A.transpose]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The normalized change-of-rings models for a compatible system map and all its levels. -/
theorem semilinearScalarData
    (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n) :
    Nonempty (ScalarData.{c, v, max c v r}
      (systemMap.{c, v, max c v r} J B τ F σ α hα)) ∧
      ∀ n : ℕ, Nonempty (ScalarData.{c, v, max c v r} (α n)) := by
  exact ⟨scalarData_nonempty.{c, v, r} (coefficientSequenceTopology J)
    (systemMap.{c, v, max c v r} J B τ F σ α hα),
    fun n ↦ scalarData_nonempty.{c, v, r} J (α n)⟩

end WeilConjectures.SemilinearSections
