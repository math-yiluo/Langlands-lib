/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Sheaf cohomology is the right-derived evaluation in every degree

`CategoryTheory.Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ` identifies
`Hⁿ⁺¹(F)` with the `(n+1)`-st right derived functor of the evaluation at a terminal object `T`.
In degree `0`, both are the sections `F(T)`, the evaluation being left exact.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

/-- **Sheaf cohomology is right-derived evaluation.** For a terminal object `T` of the site,
`Hⁿ(F)` is the `n`-th right derived functor of the evaluation at `T`, in every degree. -/
theorem cohomology_nonempty_addEquiv_rightDerived_evaluation
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
    (T : C) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Nonempty
      (Sheaf.H F n ≃+
        (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T)).rightDerived n).obj F)) := by
  cases n with
  | zero =>
    exact ⟨(H.equiv₀ F hT).trans
      (((sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj
        (op T)).rightDerivedZeroIsoSelf.app F).symm.addCommGroupIsoToAddEquiv)⟩
  | succ n => exact cohomology_nonempty_addEquiv_rightDerived_evaluation_succ J T hT F n

end CategoryTheory.Sheaf
