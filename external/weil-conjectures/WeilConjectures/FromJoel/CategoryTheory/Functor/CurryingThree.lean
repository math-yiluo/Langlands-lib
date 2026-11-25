/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.CurryingThree

/-!
# Supplementary lemmas about currying of functors in three variables

Supplement to `Mathlib.CategoryTheory.Functor.CurryingThree`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ E : Type*} [Category C₁] [Category C₂] [Category C₃] [Category E]

@[simp]
lemma uncurry₃_obj_map (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {X Y : C₁ × C₂ × C₃} (f : X ⟶ Y) :
    (uncurry₃.obj F).map f = (((F.map f.1).app X.2.1).app X.2.2 ≫
      ((F.obj Y.1).map f.2.1).app X.2.2) ≫ ((F.obj Y.1).obj Y.2.1).map f.2.2 :=
  rfl

@[simp]
lemma uncurry₃_map_app {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ E} (f : F ⟶ G) (X : C₁ × C₂ × C₃) :
    (uncurry₃.map f).app X = ((f.app X.1).app X.2.1).app X.2.2 :=
  rfl

end Functor

end CategoryTheory
