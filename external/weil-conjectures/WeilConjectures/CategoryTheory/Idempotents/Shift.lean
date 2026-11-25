/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Monoidal.End

/-!
# Shifts on the Karoubi envelope

Let `C` be a category with a shift by an additive monoid `A`. The canonical extension functor
`functorExtension₂ C C : (C ⥤ C) ⥤ (Karoubi C ⥤ Karoubi C)` is (strictly) monoidal for the
composition of endofunctors, so that the shift of `C` extends to a shift of the Karoubi envelope:
`(K, e)⟦a⟧ = (K⟦a⟧, e⟦a⟧)`. The inclusion `C ⥤ Karoubi C` commutes with the shifts.

## Main definitions

- `CategoryTheory.Idempotents.Karoubi.hasShift`: the shift on `Karoubi C`.
- `CategoryTheory.Idempotents.toKaroubi.commShift`: `toKaroubi C` commutes with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Idempotents

open Category MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

variable (C : Type*) [Category* C]

set_option backward.isDefEq.respectTransparency.types false in
/-- The extension functor `(C ⥤ C) ⥤ (Karoubi C ⥤ Karoubi C)` is monoidal for the composition
of endofunctors: it preserves identities and compositions on the nose. -/
noncomputable instance : (functorExtension₂ C C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := NatIso.ofComponents (fun P ↦ Iso.refl _) (fun f ↦ by ext; simp)
      μIso := fun F G ↦ NatIso.ofComponents (fun P ↦ Iso.refl _) (fun f ↦ by ext; simp)
      μIso_hom_natural_left := by intros; ext; simp
      μIso_hom_natural_right := by intros; ext; simp; rfl
      associativity := by intros; ext; simp
      left_unitality := by intros; ext; simp
      right_unitality := by intros; ext; simp }

@[simp]
lemma functorExtension₂_η_app_f (P : Karoubi C) :
    ((Functor.OplaxMonoidal.η (functorExtension₂ C C)).app P).f = P.p := rfl

@[simp]
lemma functorExtension₂_ε_app_f (P : Karoubi C) :
    ((Functor.LaxMonoidal.ε (functorExtension₂ C C)).app P).f = P.p := rfl

@[simp]
lemma functorExtension₂_μ_app_f (F G : C ⥤ C) (P : Karoubi C) :
    ((Functor.LaxMonoidal.μ (functorExtension₂ C C) F G).app P).f = G.map (F.map P.p) := rfl

@[simp]
lemma functorExtension₂_δ_app_f (F G : C ⥤ C) (P : Karoubi C) :
    ((Functor.OplaxMonoidal.δ (functorExtension₂ C C) F G).app P).f = G.map (F.map P.p) := rfl

variable {C} (A : Type*) [AddMonoid A] [HasShift C A]

/-- The shift on the Karoubi envelope: `(K, e)⟦a⟧ = (K⟦a⟧, e⟦a⟧)`. -/
noncomputable instance Karoubi.hasShift : HasShift (Karoubi C) A where
  shift := HasShift.shift ⋙ functorExtension₂ C C
  shiftMonoidal := by
    have := (HasShift.shiftMonoidal : (HasShift.shift : Discrete A ⥤ C ⥤ C).Monoidal)
    infer_instance

variable {A}

@[simp]
lemma Karoubi.shiftFunctor_obj_X (P : Karoubi C) (a : A) :
    ((shiftFunctor (Karoubi C) a).obj P).X = P.X⟦a⟧ := rfl

@[simp]
lemma Karoubi.shiftFunctor_obj_p (P : Karoubi C) (a : A) :
    ((shiftFunctor (Karoubi C) a).obj P).p = P.p⟦a⟧' := rfl

@[simp]
lemma Karoubi.shiftFunctor_map_f {P Q : Karoubi C} (f : P ⟶ Q) (a : A) :
    ((shiftFunctor (Karoubi C) a).map f).f = f.f⟦a⟧' := rfl

lemma Karoubi.η_shift_app_f (P : Karoubi C) :
    ((Functor.OplaxMonoidal.η (shiftMonoidalFunctor (Karoubi C) A)).app P).f =
      (Functor.OplaxMonoidal.η (shiftMonoidalFunctor C A)).app P.X ≫ P.p := by
  change ((Functor.OplaxMonoidal.η (shiftMonoidalFunctor C A ⋙ functorExtension₂ C C)).app P).f = _
  rw [Functor.OplaxMonoidal.comp_η]
  simp

lemma Karoubi.δ_shift_app_f (a b : A) (P : Karoubi C) :
    ((Functor.OplaxMonoidal.δ (shiftMonoidalFunctor (Karoubi C) A) ⟨a⟩ ⟨b⟩).app P).f =
      (Functor.OplaxMonoidal.δ (shiftMonoidalFunctor C A) ⟨a⟩ ⟨b⟩).app P.X ≫ (P.p⟦a⟧')⟦b⟧' := by
  change ((Functor.OplaxMonoidal.δ (shiftMonoidalFunctor C A ⋙ functorExtension₂ C C)
    ⟨a⟩ ⟨b⟩).app P).f = _
  rw [Functor.OplaxMonoidal.comp_δ]
  simp only [Functor.comp_obj, endofunctorMonoidalCategory_tensorObj_obj, NatTrans.comp_app,
    Karoubi.comp_f, functorExtension₂_map_app_f, endofunctorMonoidalCategory_tensorObj_map,
    functorExtension₂_δ_app_f, assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, P.idem]
  rfl

lemma Karoubi.ε_shift_app_f (P : Karoubi C) :
    ((Functor.LaxMonoidal.ε (shiftMonoidalFunctor (Karoubi C) A)).app P).f =
      P.p ≫ (Functor.LaxMonoidal.ε (shiftMonoidalFunctor C A)).app P.X := by
  change ((Functor.LaxMonoidal.ε (shiftMonoidalFunctor C A ⋙ functorExtension₂ C C)).app P).f = _
  rw [Functor.LaxMonoidal.comp_ε]
  simp

lemma Karoubi.μ_shift_app_f (a b : A) (P : Karoubi C) :
    ((Functor.LaxMonoidal.μ (shiftMonoidalFunctor (Karoubi C) A) ⟨a⟩ ⟨b⟩).app P).f =
      (P.p⟦a⟧')⟦b⟧' ≫ (Functor.LaxMonoidal.μ (shiftMonoidalFunctor C A) ⟨a⟩ ⟨b⟩).app P.X := by
  change ((Functor.LaxMonoidal.μ (shiftMonoidalFunctor C A ⋙ functorExtension₂ C C)
    ⟨a⟩ ⟨b⟩).app P).f = _
  rw [Functor.LaxMonoidal.comp_μ]
  simp only [Functor.comp_obj, endofunctorMonoidalCategory_tensorObj_obj, NatTrans.comp_app,
    Karoubi.comp_f, functorExtension₂_μ_app_f, functorExtension₂_map_app_f]
  rw [← (Functor.LaxMonoidal.μ (shiftMonoidalFunctor C A) ⟨a⟩ ⟨b⟩).naturality P.p]
  simp only [endofunctorMonoidalCategory_tensorObj_map, ← Functor.map_comp_assoc]
  rw [← Functor.map_comp, P.idem]
  rfl

@[simp]
lemma Karoubi.shiftFunctorZero_hom_app_f (P : Karoubi C) :
    ((shiftFunctorZero (Karoubi C) A).hom.app P).f =
      (shiftFunctorZero C A).hom.app P.X ≫ P.p := by
  simp [shiftFunctorZero, Functor.Monoidal.εIso, Karoubi.η_shift_app_f]

@[simp]
lemma Karoubi.shiftFunctorZero_inv_app_f (P : Karoubi C) :
    ((shiftFunctorZero (Karoubi C) A).inv.app P).f =
      P.p ≫ (shiftFunctorZero C A).inv.app P.X := by
  simp [shiftFunctorZero, Functor.Monoidal.εIso, Karoubi.ε_shift_app_f]

@[simp]
lemma Karoubi.shiftFunctorAdd_hom_app_f (a b : A) (P : Karoubi C) :
    ((shiftFunctorAdd (Karoubi C) a b).hom.app P).f =
      (shiftFunctorAdd C a b).hom.app P.X ≫ (P.p⟦a⟧')⟦b⟧' := by
  simp [shiftFunctorAdd, Functor.Monoidal.μIso, Karoubi.δ_shift_app_f]

@[simp]
lemma Karoubi.shiftFunctorAdd_inv_app_f (a b : A) (P : Karoubi C) :
    ((shiftFunctorAdd (Karoubi C) a b).inv.app P).f =
      (P.p⟦a⟧')⟦b⟧' ≫ (shiftFunctorAdd C a b).inv.app P.X := by
  simp [shiftFunctorAdd, Functor.Monoidal.μIso, Karoubi.μ_shift_app_f]

variable (C A) in
/-- The commutation isomorphisms of `toKaroubi C` with the shifts. -/
noncomputable def toKaroubiCommShiftIso (a : A) :
    shiftFunctor C a ⋙ toKaroubi C ≅ toKaroubi C ⋙ shiftFunctor (Karoubi C) a :=
  NatIso.ofComponents (fun X ↦ { hom := ⟨𝟙 _, by simp⟩, inv := ⟨𝟙 _, by simp⟩ })
    (fun f ↦ by ext; simp)

/-- The inclusion of a category into its Karoubi envelope commutes with the shifts. -/
noncomputable instance toKaroubi.commShift : (toKaroubi C).CommShift A where
  commShiftIso a := toKaroubiCommShiftIso C A a
  commShiftIso_zero := by
    ext X
    simp [toKaroubiCommShiftIso, Functor.CommShift.isoZero_hom_app]
  commShiftIso_add a b := by
    ext X
    simp [toKaroubiCommShiftIso, Functor.CommShift.isoAdd_hom_app]

@[simp]
lemma toKaroubi_commShiftIso_hom_app_f (a : A) (X : C) :
    (((toKaroubi C).commShiftIso a).hom.app X).f = 𝟙 _ := rfl

@[simp]
lemma toKaroubi_commShiftIso_inv_app_f (a : A) (X : C) :
    (((toKaroubi C).commShiftIso a).inv.app X).f = 𝟙 _ := rfl

end CategoryTheory.Idempotents
