/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Left exactness of the pullback of abelian presheaves

For a functor `b : C ⥤ D` between small categories, the left Kan extension
`b.op.lan : (Cᵒᵖ ⥤ Ab) ⥤ (Dᵒᵖ ⥤ Ab)` (denoted `b_p` in the Stacks project) is left adjoint to
restriction along `b`, is computed pointwise by colimits over the categories `I_Y` of pairs
`(X, φ : Y ⟶ b X)`, and commutes with finite limits when `C` has finite limits and `b` preserves
them (Stacks, Tag 00XK). This is a thin restatement of Mathlib results.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace CategoryTheory

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (b : C ⥤ D)

/-- **Pullback of abelian presheaves is left exact** (Stacks, Tag 00XK).
For `b : C ⥤ D` between small categories, `b_p := b.op.lan` on presheaves of abelian groups
1. is left adjoint to `b^p` (precomposition with `b.op`), and its value at `Y` is the colimit
   over the costructured arrows `(X, Y ⟶ b X)`;
2. if `C` has finite limits and `b` preserves them, then every category
   `I_Y = StructuredArrow Y b` is cofiltered (`I_Yᵒᵖ` is filtered), `b_p` preserves finite
   limits, and in particular `b_p (ker φ) ≅ ker (b_p φ)` for every morphism `φ`.
(blueprint: `lem-weil-pbc-presheaf-pullback-left-exact`) -/
theorem lan_op_addCommGrp_adjunction_and_preservesFiniteLimits :
    Nonempty ((b.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ _) ⊣
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj b.op) ∧
      (∀ Y : D, Nonempty (b.op.lan ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op Y) ≅
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
          (CostructuredArrow.proj b.op (op Y)) ⋙ colim)) ∧
      ([HasFiniteLimits C] → [PreservesFiniteLimits b] →
        (∀ Y : D, IsFiltered (StructuredArrow Y b)ᵒᵖ) ∧
        PreservesFiniteLimits (b.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ _) ∧
        ∀ {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F₁ ⟶ F₂),
          IsIso (kernelComparison φ (b.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ _))) := by
  refine ⟨⟨b.op.lanAdjunction _⟩, fun Y ↦ ⟨lanEvaluationIsoColim _ _ _⟩, ?_⟩
  intro _ _
  have := flat_of_preservesFiniteLimits b
  refine ⟨fun Y ↦ inferInstance, inferInstance, fun φ ↦ ?_⟩
  have : (b.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ _).IsLeftAdjoint :=
    (b.op.lanAdjunction _).isLeftAdjoint
  infer_instance

end CategoryTheory
