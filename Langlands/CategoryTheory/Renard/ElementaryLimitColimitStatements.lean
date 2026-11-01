import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# Renard A.IV: elementary limit and colimit examples

The first four examples in A.IV.1 and their explicitly named A.IV.2 duals,
as closed propositions about actual Mathlib cones and cocones.
-/

universe vC uC uI

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.ElementaryLimitColimit

/-- Limits of the empty diagram are precisely terminal objects. -/
def EmptyLimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C]
    (D : Discrete.{uI} PEmpty ⥤ C) (t : Cone D),
    Nonempty (IsLimit t) ↔
      ∀ Y : C, ∃! _f : Y ⟶ t.pt, True

/-- A kernel is a limit of the parallel pair consisting of the map and zero. -/
def KernelStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
    (X Y K : C) (f : X ⟶ Y) (i : K ⟶ X) (h : i ≫ f = 0),
    Nonempty (IsLimit (KernelFork.ofι i h)) ↔
      ∀ (Z : C) (q : Z ⟶ X), q ≫ f = 0 →
        ∃! l : Z ⟶ K, l ≫ i = q

/-- Arbitrary products are limits of their discrete diagrams. -/
def ProductStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (I : Type uI) (X : I → C)
    (P : C) (p : ∀ i, P ⟶ X i),
    Nonempty (IsLimit (Fan.mk P p)) ↔
      ∀ (Y : C) (q : ∀ i, Y ⟶ X i),
        ∃! l : Y ⟶ P, ∀ i, l ≫ p i = q i

/-- Pullbacks are limits of their cospan diagrams. -/
def PullbackStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y Z P : C)
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : P ⟶ X) (q : P ⟶ Y)
    (h : p ≫ f = q ≫ g),
    Nonempty (IsLimit (PullbackCone.mk p q h)) ↔
      ∀ (W : C) (a : W ⟶ X) (b : W ⟶ Y), a ≫ f = b ≫ g →
        ∃! l : W ⟶ P, l ≫ p = a ∧ l ≫ q = b

/-- Colimits of the empty diagram are precisely initial objects. -/
def EmptyColimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C]
    (D : Discrete.{uI} PEmpty ⥤ C) (t : Cocone D),
    Nonempty (IsColimit t) ↔
      ∀ Y : C, ∃! _f : t.pt ⟶ Y, True

/-- A cokernel is a colimit of the parallel pair consisting of the map and zero. -/
def CokernelStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
    (X Y Q : C) (f : X ⟶ Y) (p : Y ⟶ Q) (h : f ≫ p = 0),
    Nonempty (IsColimit (CokernelCofork.ofπ p h)) ↔
      ∀ (Z : C) (q : Y ⟶ Z), f ≫ q = 0 →
        ∃! l : Q ⟶ Z, p ≫ l = q

/-- Arbitrary coproducts are colimits of their discrete diagrams. -/
def CoproductStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (I : Type uI) (X : I → C)
    (P : C) (p : ∀ i, X i ⟶ P),
    Nonempty (IsColimit (Cofan.mk P p)) ↔
      ∀ (Y : C) (q : ∀ i, X i ⟶ Y),
        ∃! l : P ⟶ Y, ∀ i, p i ≫ l = q i

/-- Pushouts are colimits of their span diagrams. -/
def PushoutStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y Z P : C)
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y ⟶ P) (q : Z ⟶ P)
    (h : f ≫ p = g ≫ q),
    Nonempty (IsColimit (PushoutCocone.mk p q h)) ↔
      ∀ (W : C) (a : Y ⟶ W) (b : Z ⟶ W), f ≫ a = g ≫ b →
        ∃! l : P ⟶ W, p ≫ l = a ∧ q ≫ l = b

/-- The four limit examples followed by the four corresponding colimit examples. -/
def ElementaryLimitColimitStatements : Prop :=
  EmptyLimitStatement.{vC, uC, uI} ∧
    KernelStatement.{vC, uC} ∧
    ProductStatement.{vC, uC, uI} ∧
    PullbackStatement.{vC, uC} ∧
    EmptyColimitStatement.{vC, uC, uI} ∧
    CokernelStatement.{vC, uC} ∧
    CoproductStatement.{vC, uC, uI} ∧
    PushoutStatement.{vC, uC}

end Langlands.Renard.ElementaryLimitColimit
