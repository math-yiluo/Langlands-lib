/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Functors induced between triangulated subcategories

For full subcategories `P` of `C` and `Q` of `D`, both stable under the shift, a functor
`F : C ⥤ D` commuting with the shifts and carrying `P` into `Q` induces a functor
`P.liftFullSubcategory Q F h` commuting with the shifts; it is triangulated if `F` is and `P`, `Q`
are triangulated subcategories.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C) (Q : ObjectProperty D)

section CommShift

variable {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [P.IsStableUnderShift A]
  [Q.IsStableUnderShift A] (F : C ⥤ D) [F.CommShift A] (h : ∀ X, P X → Q (F.obj X))

noncomputable instance commShiftLiftFullSubcategory :
    (P.liftFullSubcategory Q F h).CommShift A :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) fun X ↦ h X.obj X.property).CommShift A)

instance : NatTrans.CommShift (P.liftFullSubcategoryCompιIso Q F h).hom A :=
  inferInstanceAs (NatTrans.CommShift
    ((Q.liftCompιIso (P.ι ⋙ F) fun X ↦ h X.obj X.property).hom) A)

end CommShift

instance isTriangulated_liftFullSubcategory [HasZeroObject C] [HasZeroObject D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    [P.IsTriangulated] [Q.IsTriangulated] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (h : ∀ X, P X → Q (F.obj X)) :
    (P.liftFullSubcategory Q F h).IsTriangulated :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) fun X ↦ h X.obj X.property).IsTriangulated)

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- **Restriction of a triangulated functor to triangulated subcategories.** Let `F : C ⥤ D` be
a triangulated functor and `S`, `S'` triangulated subcategories of `C`, `D` with `F` sending `S`
into `S'`. Then the restriction `S ⥤ S'` of `F` (`S'.lift (S.ι ⋙ F) hF`) is triangulated, and
its composite with the inclusion of `S'` is `S.ι ⋙ F`.
(blueprint: `situation-conventions`) -/
theorem isTriangulated_lift_ι_comp (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : ObjectProperty C) [S.IsTriangulated] (S' : ObjectProperty D) [S'.IsTriangulated]
    (hF : ∀ X : S.FullSubcategory, S' (F.obj X.obj)) :
    (S'.lift (S.ι ⋙ F) hF).IsTriangulated ∧ S'.lift (S.ι ⋙ F) hF ⋙ S'.ι = S.ι ⋙ F :=
  ⟨inferInstance, rfl⟩


end CategoryTheory.ObjectProperty
