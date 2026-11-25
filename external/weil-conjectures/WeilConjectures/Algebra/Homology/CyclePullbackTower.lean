/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The actual descending cycle-pullback tower

Source: Stacks Project, Derived Categories, Lemma 05T7 (1). We perform its recursion in
an abelian functor category. No object is selected from an unproved existence theorem.
(blueprint: def-pc-cycle-pullback-tower-data-stage3).
-/

@[expose] public section

universe v u vB uB

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.CyclePullback

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B]

/-- Evaluation of a family of complexes in degree `i`. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
def targetTerm (F : B ⥤ CochainComplex A ℤ) (i : ℤ) : B ⥤ A :=
  F ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i

/-- A differential of a family of complexes, as a natural transformation. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
def targetD (F : B ⥤ CochainComplex A ℤ) (i j : ℤ) :
    targetTerm F i ⟶ targetTerm F j :=
  Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (ComplexShape.up ℤ) i j)

/-- The zero family used above the bound. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def zeroTerm : B ⥤ A := (Functor.const B).obj (0 : A)

/-- The two terms and augmentation needed to perform one descending step. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
structure Stage (F : B ⥤ CochainComplex A ℤ) where
  degree : ℤ
  current : B ⥤ A
  next : B ⥤ A
  d : current ⟶ next
  e : current ⟶ targetTerm F degree

/-- The initial stage consists of two zero families above the bound. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def initial (F : B ⥤ CochainComplex A ℤ) (N : ℤ) : Stage F where
  degree := N + 1
  current := zeroTerm
  next := zeroTerm
  d := 0
  e := 0

/-- The cospan's right arrow: next cycles followed by the next augmentation. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def cyclesArrow {F : B ⥤ CochainComplex A ℤ} (s : Stage F) :
    kernel s.d ⟶ targetTerm F s.degree := kernel.ι s.d ≫ s.e

/-- The pullback formed at a descending step. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def stepPullback {F : B ⥤ CochainComplex A ℤ} (s : Stage F) : B ⥤ A :=
  pullback (targetD F (s.degree - 1) s.degree) (cyclesArrow s)

/-- One descending step, with precisely the prescribed object and projections. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def step (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {F : B ⥤ CochainComplex A ℤ} (s : Stage F) : Stage F where
  degree := s.degree - 1
  current := stepPullback s ⋙ T
  next := s.current
  d := Functor.whiskerLeft (stepPullback s) π ≫
    pullback.snd (targetD F (s.degree - 1) s.degree) (cyclesArrow s) ≫ kernel.ι s.d
  e := Functor.whiskerLeft (stepPullback s) π ≫
    pullback.fst (targetD F (s.degree - 1) s.degree) (cyclesArrow s)

/-- Iterate the explicit step. Stage `k` starts in degree `N + 1 - k`. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def tower (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) : ℕ → Stage F
  | 0 => initial F N
  | k + 1 => step T π (tower T π F N k)

/-- The degree decreases by one at each step. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem tower_degree (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (k : ℕ) :
    (tower T π F N k).degree = N + 1 - (k : ℤ) := by
  induction k with
  | zero => simp [tower, initial]
  | succ k hk => simp only [tower, step, hk, Nat.cast_add, Nat.cast_one]; omega

/-- The natural-number index of the stage supplying degree `i`. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
def depth (N i : ℤ) : ℕ := (N - i).toNat + 1

/-- The integer-indexed term family, with literal zero objects above the bound. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def term (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) : B ⥤ A :=
  if i ≤ N then (tower T π F N (depth N i)).current else zeroTerm

/-- The successor term of a stage is the family in the next integer degree. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem tower_next (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    (tower T π F N (depth N i)).next = term T π F N (i + 1) := by
  by_cases h : i = N
  · subst i
    simp [depth, tower, step, initial, term, zeroTerm]
  · have h' : i + 1 ≤ N := by omega
    have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
    rw [hd]
    simp only [tower, step, term, ite_eq_left h']

/-- The current term is identified with the selected stage's current family. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem term_eq (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    term T π F N i = (tower T π F N (depth N i)).current := by
  simp only [term, ite_eq_left hi]

/-- The chosen stage has the requested integer degree. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem degree_eq (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    (tower T π F N (depth N i)).degree = i := by
  rw [tower_degree]
  unfold depth
  omega

/-- The adjacent differential, transported only across proved equalities of families. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def differential (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) :
    term T π F N i ⟶ term T π F N (i + 1) :=
  if hi : i ≤ N then
    eqToHom (term_eq T π F N i hi) ≫ (tower T π F N (depth N i)).d ≫
      eqToHom (tower_next T π F N i hi)
  else 0

/-- The augmentation, transported to evaluation in the requested degree. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
noncomputable def augmentation (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) :
    term T π F N i ⟶ targetTerm F i :=
  if hi : i ≤ N then
    eqToHom (term_eq T π F N i hi) ≫ (tower T π F N (depth N i)).e ≫
      eqToHom (congrArg (targetTerm F) (degree_eq T π F N i hi))
  else 0

/-- Above the bound the term is the constant zero family. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem term_isZero (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : N < i) (b : B) :
    IsZero ((term T π F N i).obj b) := by
  simp only [term, ite_eq_right (by omega : ¬ i ≤ N), zeroTerm, Functor.const_obj_obj]
  exact isZero_zero A

/-- The term property follows directly from the construction, without a resolution theorem. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem term_mem (S : ObjectProperty A) (hzero : ∀ X : A, IsZero X → S X)
    (T : A ⥤ A) (π : T ⟶ 𝟭 A) (hT : ∀ X : A, S (T.obj X))
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (b : B) :
    S ((term T π F N i).obj b) := by
  by_cases hi : i ≤ N
  · simp only [term, ite_eq_left hi, depth, tower, step, Functor.comp_obj]
    exact hT _
  · exact hzero _ (term_isZero T π F N i (by omega) b)

/-- The local descending step squares to zero by the kernel equation. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem step_square (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {F : B ⥤ CochainComplex A ℤ} (s : Stage F) :
    (step T π s).d ≫ s.d = 0 := by
  simp only [step, Category.assoc, kernel.condition, comp_zero]

/-- The local descending step commutes with augmentation by the pullback equation. 
(blueprint: def-pc-cycle-pullback-tower-data-stage3)
-/
theorem step_comm (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {F : B ⥤ CochainComplex A ℤ} (s : Stage F) :
    (step T π s).e ≫ targetD F (s.degree - 1) s.degree = (step T π s).d ≫ s.e := by
  dsimp only [step]
  rw [Category.assoc, pullback.condition]
  simp only [cyclesArrow, Category.assoc]

end CochainComplex.CyclePullback
