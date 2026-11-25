/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.IrreducibleDef

/-! # A component API for the clopen comparison composite

Source: the functorial composite in Stacks Tag 0F7B, first proof paragraph
(blueprint: def-cbc-clopen-mate-composite).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory

/-- Compose the base-change map, clopen projection, and two compositors.
This is the component form of their whiskered composite; naturality follows by
naturality of those maps and functoriality.
Source: Stacks Tag 0F7B (blueprint: def-cbc-clopen-mate-composite). -/
noncomputable irreducible_def clopenMateComposite.{v₁, u₁, v₂, u₂, v₃, u₃, v₄, u₄, v₅, u₅}
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D] [Category.{v₅} E]
    (U : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : U ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) : U ⋙ P ⟶ R ⋙ K :=
  { app F := β.app F ≫ B₀.map (π.app (Q.obj F)) ≫ c.app (S.obj (Q.obj F)) ≫
      K.map (d.app F)
    naturality _ _ f :=
      (β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) B₀ ≫
        Functor.whiskerLeft (Q ⋙ S) c ≫ Functor.whiskerRight d K).naturality f }

variable {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
  [Category* D] [Category* E]

/-- Evaluation of the clopen comparison composite.
Expand composition and whiskering of natural transformations.
Source: Stacks Tag 0F7B (blueprint: def-cbc-clopen-mate-composite). -/
theorem clopenMateComposite_app
    (U : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : U ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) (F : A) :
    (clopenMateComposite U P Q S J B₀ K R β π c d).app F =
      β.app F ≫ B₀.map (π.app (Q.obj F)) ≫ c.app (S.obj (Q.obj F)) ≫
        K.map (d.app F) := by
  rw [clopenMateComposite_def]

end CategoryTheory
