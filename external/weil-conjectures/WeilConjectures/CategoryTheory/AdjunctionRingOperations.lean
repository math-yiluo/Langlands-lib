/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Product operations and the Hom adjunction

The adjunct of a transported operation is the operation on the adjuncts.
Source: Stacks Project, Modules on Sites, Tag 03CR, induced module direct image.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  {L : D ⥤ C} {V : C ⥤ D} (adj : L ⊣ V)
  [PreservesFiniteProducts V]

/-- The counit converts an inverse terminal comparison into the terminal map. -/
theorem counit_constant {A : C} (o : 𝟙_ C ⟶ A) (T : D) :
    L.map (toUnit T ≫ (preservesTerminalIso V).inv ≫ V.map o) ≫ adj.counit.app A =
      toUnit (L.obj T) ≫ o := by
  simp only [Functor.map_comp, Category.assoc]
  rw [show L.map (V.map o) ≫ adj.counit.app A = adj.counit.app _ ≫ o from
    adj.counit.naturality o]
  simp only [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ o)
  exact toUnit_unique _ _


/-- The counit converts inverse product comparisons into the product of counits. -/
theorem counit_pair {A B X : C} (o : A ⊗ B ⟶ X) {T : D}
    (x : T ⟶ V.obj A) (y : T ⟶ V.obj B) :
    L.map (lift x y ≫ (prodComparisonIso V A B).inv ≫ V.map o) ≫ adj.counit.app X =
      lift (L.map x ≫ adj.counit.app A) (L.map y ≫ adj.counit.app B) ≫ o := by
  simp only [Functor.map_comp, Category.assoc]
  rw [show L.map (V.map o) ≫ adj.counit.app X = adj.counit.app _ ≫ o from
    adj.counit.naturality o]
  simp only [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ o)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [← adj.counit_naturality]
    have hc : (prodComparisonIso V A B).inv ≫ V.map (fst A B) = fst _ _ :=
      (cancel_epi (prodComparisonIso V A B).hom).mp (by
        rw [Iso.hom_inv_id_assoc]
        exact (CartesianMonoidalCategory.prodComparison_fst V A B).symm)
    rw [← Category.assoc (L.map _) (L.map _) (adj.counit.app A), ← L.map_comp, hc]
    rw [← Category.assoc, ← L.map_comp, lift_fst]
    exact (lift_fst _ _).symm
  · simp only [Category.assoc]
    rw [← adj.counit_naturality]
    have hc : (prodComparisonIso V A B).inv ≫ V.map (snd A B) = snd _ _ :=
      (cancel_epi (prodComparisonIso V A B).hom).mp (by
        rw [Iso.hom_inv_id_assoc]
        exact (CartesianMonoidalCategory.prodComparison_snd V A B).symm)
    rw [← Category.assoc (L.map _) (L.map _) (adj.counit.app B), ← L.map_comp, hc]
    rw [← Category.assoc, ← L.map_comp, lift_snd]
    exact (lift_snd _ _).symm

/-- The counit respects a binary operation on one object. -/
theorem counit_binary {A : C} (o : A ⊗ A ⟶ A) {T : D}
    (x y : T ⟶ V.obj A) :
    L.map (lift x y ≫ (prodComparisonIso V A A).inv ≫ V.map o) ≫ adj.counit.app A =
      lift (L.map x ≫ adj.counit.app A) (L.map y ≫ adj.counit.app A) ≫ o :=
  adj.counit_pair o x y

end CategoryTheory.Adjunction
