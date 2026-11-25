/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The constant sheaf functor is monoidal

The constant presheaf functor `A ⥤ (Cᵒᵖ ⥤ A)` is monoidal for the pointwise tensor product of
presheaves (`CategoryTheory.Functor.Monoidal.const`), so the constant sheaf functor, its
composite with sheafification, is monoidal for the monoidal structure
`CategoryTheory.Sheaf.monoidalCategory` on sheaves
(`CategoryTheory.monoidalConstantSheaf`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]
  [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory in
/-- The constant sheaf functor is monoidal for the monoidal structure
`CategoryTheory.Sheaf.monoidalCategory` on sheaves: it is the composite of the constant
presheaf functor and of sheafification, which are both monoidal. -/
noncomputable instance monoidalConstantSheaf : (constantSheaf J A).Monoidal :=
  inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Monoidal

end CategoryTheory
