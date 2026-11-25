/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Evaluation normalization for a contravariant internal Hom shift -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory Opposite

namespace CategoryTheory

/-- Evaluation normalization for the quadratic-signed contravariant Hom shift.
Source: Stacks Project, Tag 08JC, tensor-Hom shift adjunction.
This is the explicit equation obtained by applying tensorLeft(K[-n]) to the
signed Hom shift, cancelling the opposite tensor shifts, and evaluating. It is a
predicate on a specified coherent shift, and chooses no objects or morphisms.
(blueprint: def-coef-hom-shift-evaluation-normalization) -/
def homShiftEvaluationNormalization
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
    (M : D) (s : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ) : Prop :=
  letI := s
  ∀ (K : D) (n : ℤ),
    ((curriedTensor D).obj (K⟦-n⟧)).map
        ((n * (n + 1) / 2).negOnePow •
          ((MonoidalClosed.internalHom.flip.obj M).commShiftIso n).hom.app (op K)) ≫
      (show ((curriedTensor D).obj (K⟦-n⟧)).obj
            (((MonoidalClosed.internalHom.flip.obj M).obj (op K))⟦n⟧) ⟶
          ((curriedTensor D).obj K).obj
            ((MonoidalClosed.internalHom.flip.obj M).obj (op K)) from
        (((curriedTensor D).flip.obj
            (((MonoidalClosed.internalHom.flip.obj M).obj (op K))⟦n⟧)).commShiftIso
              (-n)).hom.app K ≫
          ((((curriedTensor D).obj K).commShiftIso n).hom.app
            ((MonoidalClosed.internalHom.flip.obj M).obj (op K)))⟦-n⟧' ≫
          (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _) ≫
      (MonoidalClosed.internalHomAdjunction₂.adj K).counit.app M =
    (MonoidalClosed.internalHomAdjunction₂.adj (K⟦-n⟧)).counit.app M

end CategoryTheory
