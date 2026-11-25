/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The left adjoint of a lax braided functor is oplax braided

For an adjunction `F ⊣ G` whose right adjoint `G` is lax braided, the oplax monoidal structure
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal` on the left adjoint `F` is compatible with
the braidings (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_δ_braiding`). Hence if this
oplax structure is invertible, `F` is braided
(`CategoryTheory.Functor.Monoidal.μ_braiding_of_δ_braiding`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxBraided]

/-- The oplax monoidal structure on the left adjoint of a lax braided functor is compatible with
the braidings. -/
lemma leftAdjointOplaxMonoidal_δ_braiding (X Y : C) :
    letI := adj.leftAdjointOplaxMonoidal
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X := by
  let := adj.leftAdjointOplaxMonoidal
  rw [leftAdjointOplaxMonoidal_δ, leftAdjointOplaxMonoidal_δ,
    ← homEquiv_naturality_right_symm, ← homEquiv_naturality_left_symm, Category.assoc,
    Functor.LaxBraided.braided, ← BraidedCategory.braiding_naturality_assoc]
  rfl

end Adjunction

namespace Functor.Monoidal

/-- A monoidal functor whose oplax structure `δ` is compatible with the braidings is braided. -/
lemma μ_braiding_of_δ_braiding {F : C ⥤ D} [F.Monoidal]
    (h : ∀ X Y : C, δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X)
    (X Y : C) : μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← cancel_mono (δ F Y X), Category.assoc, ← h, μ_δ_assoc, Category.assoc, μ_δ,
    Category.comp_id]

end Functor.Monoidal

end CategoryTheory
