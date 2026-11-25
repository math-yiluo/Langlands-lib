/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Extending a natural comparison from a resolving class

Source: Stacks Project, Tag 06YJ, resolving-class argument, and Tag 04VC,
right fractions. (blueprint: lem-sc-nattrans-from-resolving-class).
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory
namespace CategoryTheory

/-- A comparison out of a functor inverting weak equivalences extends from a full
resolving class. The target functor need not invert weak equivalences.

Source: Stacks Project, Tags 06YJ and 04VC, resolving-class and right-fraction arguments.
Proof. Choose a resolution s_X : P_X → X. Set β_X = A(s_X)⁻¹ α_P_X B(s_X).
For any arrow t : P → X from a resolving object, the right Ore condition supplies
a common source for t and s_X. Resolve that source once more. Naturality of α
on the resulting two arrows and cancellation of A of the weak equivalence show
A(t) β_X = α_P B(t). Applying this formula to a resolution of the source of an
arbitrary arrow proves naturality of β. Applying it to an identity proves β_P = α_P.
The argument uses only invertibility of A(s), and therefore also works for zero
objects and for a resolving class containing all objects.
(blueprint: lem-sc-nattrans-from-resolving-class). -/
theorem exists_natTrans_from_resolvingClass
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : C → Prop)
    (hres : ∀ X : C, ∃ (R : C) (s : R ⟶ X), P R ∧ W s)
    (A B : C ⥤ D) (hA : W.IsInvertedBy A)
    (α : ∀ X : C, P X → (A.obj X ⟶ B.obj X))
    (hα : ∀ (X Y : C) (hX : P X) (hY : P Y) (s : X ⟶ Y),
      A.map s ≫ α Y hY = α X hX ≫ B.map s) :
    ∃ β : A ⟶ B, ∀ (X : C) (hX : P X), β.app X = α X hX := by
  classical
  choose R s hR hs using hres
  have hiso (X : C) : IsIso (A.map (s X)) := hA _ (hs X)
  let β (X : C) : A.obj X ⟶ B.obj X :=
    inv (A.map (s X)) ≫ α (R X) (hR X) ≫ B.map (s X)
  have hchosen (X : C) :
      A.map (s X) ≫ β X = α (R X) (hR X) ≫ B.map (s X) := by
    dsimp only [β]
    simp
  have hfac (X Y : C) (hX : P X) (t : X ⟶ Y) :
      A.map t ≫ β Y = α X hX ≫ B.map t := by
    obtain ⟨z, hz⟩ := (MorphismProperty.LeftFraction.mk t (s Y) (hs Y)).exists_rightFraction
    let a := s z.X' ≫ z.s
    let b := s z.X' ≫ z.f
    have hab : a ≫ t = b ≫ s Y := by
      dsimp only [a, b]
      rw [Category.assoc, hz, ← Category.assoc]
    have ha : W a := W.comp_mem _ _ (hs z.X') z.hs
    have : IsIso (A.map a) := hA _ ha
    apply (cancel_epi (A.map a)).1
    calc
      A.map a ≫ A.map t ≫ β Y = A.map b ≫ A.map (s Y) ≫ β Y := by
        rw [← A.map_comp_assoc, hab, A.map_comp_assoc]
      _ = A.map b ≫ α (R Y) (hR Y) ≫ B.map (s Y) := by rw [hchosen]
      _ = α (R z.X') (hR z.X') ≫ B.map b ≫ B.map (s Y) := by
        rw [← Category.assoc, hα _ _ (hR z.X') (hR Y) b, Category.assoc]
      _ = α (R z.X') (hR z.X') ≫ B.map a ≫ B.map t := by
        rw [← B.map_comp, ← hab, B.map_comp]
      _ = A.map a ≫ α X hX ≫ B.map t := by
        rw [← Category.assoc, ← hα _ _ (hR z.X') hX a, Category.assoc]
  refine ⟨{ app := β, naturality := ?_ }, ?_⟩
  · intro X Y f
    apply (cancel_epi (A.map (s X))).1
    calc
      A.map (s X) ≫ A.map f ≫ β Y = A.map (s X ≫ f) ≫ β Y := by
        rw [A.map_comp, Category.assoc]
      _ = α (R X) (hR X) ≫ B.map (s X ≫ f) := hfac _ _ (hR X) _
      _ = (A.map (s X) ≫ β X) ≫ B.map f := by
        rw [B.map_comp, hchosen, Category.assoc]
      _ = A.map (s X) ≫ β X ≫ B.map f := Category.assoc _ _ _
  · intro X hX
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using hfac X X hX (𝟙 X)

end CategoryTheory
