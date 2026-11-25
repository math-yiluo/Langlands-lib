/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor

import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Evaluation of a K-injective complex of inverse systems is K-injective.
Source: Stacks Project, Derived Categories, Tag 070M, and the exact-adjoint
criterion `Adjunction.preservesKInjectiveComplexes`.

Proof: The left adjoint to evaluation at n sends X at m to the coproduct of
copies of X indexed by morphisms n to m. This index type is subsingleton, hence
finite. Its finite coproduct functor is exact in an abelian category. Evaluation
computes finite limits pointwise, so the left adjoint preserves finite limits;
it preserves colimits by adjunction and is additive. The exact-adjoint criterion
therefore makes evaluation preserve K-injectivity. Mapping a complex by this
functor is definitionally its evaluated complex.
(blueprint: lem-weil-tower-evaluation-kinjective)
-/
theorem tower_evaluation_isKInjective
    (A : Type u) [Category.{v} A] [Abelian A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (n : ℕᵒᵖ) :
    CochainComplex.IsKInjective (I.asFunctor.obj n) := by
  classical
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let G := evaluationLeftAdjoint A n
  have (m : ℕᵒᵖ) : PreservesFiniteLimits (G ⋙ (evaluation ℕᵒᵖ A).obj m) := by
    let e : G ⋙ (evaluation ℕᵒᵖ A).obj m ≅
        Functor.const (Discrete (n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [G, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits G := ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation G J (fun m ↦ inferInstance)⟩
  have : G.Additive := leftExactFunctor_le_additiveFunctor A (ℕᵒᵖ ⥤ A) G
    (by rw [leftExactFunctor_iff]; infer_instance)
  have : G.IsLeftAdjoint := (evaluationAdjunctionRight A n).isLeftAdjoint
  have : (evaluationLeftAdjoint A n).PreservesHomology := inferInstanceAs G.PreservesHomology
  have := (evaluationAdjunctionRight A n).preservesKInjectiveComplexes
  change CochainComplex.IsKInjective
    ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I)
  infer_instance

end CategoryTheory
