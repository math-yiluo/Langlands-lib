/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Internal hom comparison maps of restrictions to full monoidal closed subcategories

Let `P` and `Q` be monoidal closed properties of objects of monoidal closed categories `C` and
`D`, and `F : C ⥤ D` a strong monoidal functor sending objects satisfying `P` to objects
satisfying `Q`. The comparison maps `G [A, B] ⟶ [G A, G B]` of the restriction
`G = Q.lift (P.ι ⋙ F) hF` are those of `F`
(`CategoryTheory.ObjectProperty.ihomComparison_monoidalLift_app_hom`); in particular they are
isomorphisms if those of `F` are
(`CategoryTheory.ObjectProperty.isIso_ihomComparison_monoidalLift`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  [Category* D] [MonoidalCategory D] [MonoidalClosed D]
  {P : ObjectProperty C} [P.IsMonoidal] [P.IsMonoidalClosed]
  {Q : ObjectProperty D} [Q.IsMonoidal] [Q.IsMonoidalClosed]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- Currying in a full monoidal closed subcategory is currying in the ambient category. -/
lemma curry_hom {A X Y : Q.FullSubcategory} (f : A ⊗ X ⟶ Y) :
    (curry f).hom = curry f.hom :=
  rfl

/-- The comparison maps `G [A, B] ⟶ [G A, G B]` of the restriction `G = Q.lift (P.ι ⋙ F) hF`
of a strong monoidal functor `F` to full monoidal closed subcategories are those of `F`. -/
lemma ihomComparison_monoidalLift_app_hom (A B : P.FullSubcategory) :
    ((ihomComparison (Q.lift (P.ι ⋙ F) hF) A).app B).hom =
      (ihomComparison F A.obj).app B.obj := by
  rw [ihomComparison_app_eq_curry, ihomComparison_app_eq_curry, curry_hom]
  rfl

/-- The comparison maps of the restriction `Q.lift (P.ι ⋙ F) hF` of a strong monoidal functor
`F` to full monoidal closed subcategories are isomorphisms if those of `F` are. -/
lemma isIso_ihomComparison_monoidalLift (A : P.FullSubcategory)
    (h : ∀ B : P.FullSubcategory,
      IsIso ((ihomComparison F A.obj).app B.obj)) :
    IsIso (ihomComparison (Q.lift (P.ι ⋙ F) hF) A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  rw [← isIso_iff_of_reflects_iso _ Q.ι]
  rw [ι_map, ihomComparison_monoidalLift_app_hom]
  exact h B

end CategoryTheory.ObjectProperty
