/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!
# The symmetric monoidal structure on sheaf categories over an essentially small site

If the coefficient category `A` is symmetric monoidal closed, the braided monoidal structure
`CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall` on `A`-valued
sheaves on an essentially small site is symmetric (`CategoryTheory.Sheaf.symmetricCategory`).
The underlying braiding is definitionally the one of
`CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall`
(`toBraidedCategory_symmetricCategory_sheaf_of_essentiallySmall`).
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]

lemma toBraidedCategory_symmetricCategory_sheaf_of_essentiallySmall :
    (symmetricCategory_sheaf_of_essentiallySmall J (A := A)).toBraidedCategory =
      braidedCategory_sheaf_of_essentiallySmall A J :=
  rfl

end CategoryTheory.GrothendieckTopology
