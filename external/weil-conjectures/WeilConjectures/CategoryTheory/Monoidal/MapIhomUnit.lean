/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Monoidal functors preserve duals of dualizable objects

Let `F : C ⥤ D` be a strong monoidal functor between braided monoidal closed categories. For a
dualizable object `X` of `C`, the internal dual `[X, 𝟙]` is the right dual `Xᘁ`
(`CategoryTheory.MonoidalCategory.ihomUnitIsoRightDual`), and `F` sends the exact pairing of `X`
and `Xᘁ` to an exact pairing of `F X` and `F Xᘁ` (`CategoryTheory.ExactPairing.map`). Hence
`F [X, 𝟙] ≅ [F X, 𝟙]` (`CategoryTheory.Functor.mapIhomUnitIsoOfIsDualizable`), without assuming
that `F` commutes with internal homs in general.
-/

@[expose] public section

namespace CategoryTheory.Functor

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal]

/-- A monoidal functor between braided monoidal closed categories commutes with the internal
duals of dualizable objects: `F [X, 𝟙] ≅ F Xᘁ ≅ [F X, 𝟙]`. -/
noncomputable def mapIhomUnitIsoOfIsDualizable {X : C} (hX : IsDualizable X) :
    F.obj ((ihom X).obj (𝟙_ C)) ≅ (ihom (F.obj X)).obj (𝟙_ D) :=
  letI : HasRightDual X := hX.some
  letI : HasRightDual (F.obj X) :=
    { rightDual := F.obj Xᘁ
      exact := ExactPairing.map F X Xᘁ }
  F.mapIso (ihomUnitIsoRightDual X) ≪≫ (ihomUnitIsoRightDual (F.obj X)).symm

end CategoryTheory.Functor
