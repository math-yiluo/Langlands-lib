/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction

/-! # Pure tensors and the actual horizontal restrictions

## References

* Zheng Construction 4.1
* Stacks Tags 03EK and 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] evaluation transition tensorSection ordinaryEvaluationTensor
attribute [local irreducible] coefficientMap systemRing evalSection rings ringPresheaf
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence Prod.sectR
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] SheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalarsObj
attribute [local implicit_reducible] PresheafOfModules.presheaf ModuleCat.restrictScalars
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_tensor_transition_cast {m n : ℕ} (h : n ≤ m)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x₀ : M.val.obj (op (m, U.unop))) (y₀ : N.val.obj (op (m, U.unop))) :
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
        (((transition.{c, v, max c v r} J B τ h).app
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
            (systemRing J B τ) M N)).val.app U
          ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
            (tensorSection.{c, v, r} J (B m) _ _ U
              (evalSection.{c, v, r} J B τ m M U x₀)
              (evalSection.{c, v, r} J B τ m N U y₀)))) =
      tensorSection.{c, v, r} J (B n) _ _ U
        (((transition.{c, v, max c v r} J B τ h).app M).val.app U
          (evalSection.{c, v, r} J B τ m M U x₀))
        (((transition.{c, v, max c v r} J B τ h).app N).val.app U
          (evalSection.{c, v, r} J B τ m N U y₀)) := by
  let T := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) M N
  let f := (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  have h₁ := evaluation_inv_pure_cast.{c, v, r} J B τ m M N U x₀ y₀
  have h₂ := transition_apply_cast.{c, v, r} J B τ h T U
    (tensorSection.{c, v, r} (coefficientSequenceTopology J)
      (systemRing J B τ) M N (op (m, U.unop)) x₀ y₀)
  have h₃ := tensorSection_restrict.{c, v, r} (coefficientSequenceTopology J)
    (R := systemRing J B τ) M N f x₀ y₀
  have h₄ := evaluation_pure_cast.{c, v, r} J B τ n M N U
    (M.val.map f x₀) (N.val.map f y₀)
  have h₅ := transition_apply_cast.{c, v, r} J B τ h M U x₀
  have h₆ := transition_apply_cast.{c, v, r} J B τ h N U y₀
  exact (congrArg (fun z ↦
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      (((transition.{c, v, max c v r} J B τ h).app T).val.app U z)) h₁).trans
    ((congrArg ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U)
      h₂).trans
      ((congrArg (fun z ↦
        (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
          (evalSection.{c, v, r} J B τ n T U z)) h₃).trans
        (h₄.trans (congrArg₂
          (tensorSection.{c, v, r} J (B n) _ _ U) h₅ h₆).symm)))

/-- Evaluation of the actual horizontal tensor restriction preserves pure tensors.
Choose the corresponding sections on the coefficient-sequence site. The evaluation
tensor isomorphism takes their pure tensor to the evaluated pure tensor. Restriction
of the sheaf tensor pairing is the pairing of the restrictions, and the actual
horizontal map is this restriction under the evaluation section identifications.
Transport these equalities back to arbitrary evaluated sections. -/
theorem evaluation_tensor_transition_pure {m n : ℕ} (h : n ≤ m)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ m).obj N).val.obj U) :
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      (((transition.{c, v, max c v r} J B τ h).app _).val.app U
        ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
          (tensorSection.{c, v, r} J (B m) _ _ U x y))) =
      tensorSection.{c, v, r} J (B n) _ _ U
        (((transition.{c, v, max c v r} J B τ h).app M).val.app U x)
        (((transition.{c, v, max c v r} J B τ h).app N).val.app U y) := by
  obtain ⟨x₀, hx⟩ := evalSection_surjective.{c, v, r} J B τ m M U x
  obtain ⟨y₀, hy⟩ := evalSection_surjective.{c, v, r} J B τ m N U y
  let T := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) M N
  have hc := evaluation_tensor_transition_cast.{c, v, r} J B τ h M N U x₀ y₀
  exact (congrArg₂ (fun a b ↦
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      (((transition.{c, v, max c v r} J B τ h).app T).val.app U
        ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
          (tensorSection.{c, v, r} J (B m) _ _ U a b)))) hx hy).symm.trans
    (hc.trans (congrArg₂ (fun a b ↦ tensorSection.{c, v, r} J (B n) _ _ U
      (((transition.{c, v, max c v r} J B τ h).app M).val.app U a)
      (((transition.{c, v, max c v r} J B τ h).app N).val.app U b)) hx hy))

end WeilConjectures.SemilinearSections
