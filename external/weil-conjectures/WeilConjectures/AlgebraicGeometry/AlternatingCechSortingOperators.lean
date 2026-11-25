/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Explicit sorting and contraction operators on Čech cochains

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equations 20.23.6.1 and
20.23.6.2. (blueprint: def-pc-alternating-cech-sorting-operators)

All operators are finite sums with decidable filters. No sorting permutation or
homotopy is selected from an unproved existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The sorting permutation orders equal entries by their original positions.
Source: Stacks 01FM. (blueprint: def-pc-alternating-cech-sorting-operators) -/
def cechStableSort {I : Type v} [LinearOrder I] {n : ℕ} (t : Fin n → I)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Monotone (t ∘ σ) ∧ ∀ i j, i < j → t (σ i) = t (σ j) → σ i < σ j

/-- A partial sorting permutation fixes the sorted prefix and orders the remaining
original positions. Source: Stacks 01FM.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
def cechPartialSort {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (a : Fin n) : Prop :=
  (∀ k, k.val < a.val → τ k = σ k) ∧
    ∀ i j, a.val ≤ i.val → i < j → τ i < τ j

/-- The junction tuple in the first homotopy, as a map of positions.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
def cechJunction {p : ℕ} (σ τ : Equiv.Perm (Fin (p + 1))) (a : Fin (p + 1))
    (k : Fin (p + 2)) : Fin (p + 1) :=
  if h : k.val ≤ a.val then σ ⟨k.val, lt_of_le_of_lt h a.isLt⟩
  else τ ⟨k.val - 1, by omega⟩

/-- The first adjacent equality, with a strictly increasing prefix.
Source: Stacks 01FM, equation 20.23.6.2.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
def cechFirstRepeat {I : Type v} [LinearOrder I] {p : ℕ} (t : Fin (p + 1) → I)
    (a : Fin (p + 1)) : Prop :=
  ∃ h : a.val + 1 < p + 1, t a = t ⟨a.val + 1, h⟩ ∧
    ∀ (b : Fin (p + 1)) (hb : b.val < a.val),
      t b < t ⟨b.val + 1, by omega⟩

variable (X : Scheme.{u}) {I : Type v} [LinearOrder I]
  (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
  (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))

/-- Signed stable sorting, as an actual homomorphism in each degree.
Source: Stacks 01FM, the operator κ.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechStableSortingMap (p : ℕ) : S.cochains F p ⟶ S.cochains F p := by
  classical
  exact AddCommGrpCat.ofHom
    { toFun := fun s t ↦ ∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort t σ then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0
      map_zero' := by funext t; simp
      map_add' := by
        intro s s'
        funext t
        simp only [Pi.add_apply, map_add, smul_add]
        simp only [ite_add_zero, Finset.sum_add_distrib] }

/-- Signed extension of increasing restriction, zero on tuples with repetitions.
Source: Stacks 01FK and 01FM, the operator cπ.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechAlternatingProjectionMap (p : ℕ) :
    S.cochains F p ⟶ S.cochains F p := by
  classical
  exact AddCommGrpCat.ofHom
    { toFun := fun s t ↦ ∑ σ : Equiv.Perm (Fin (p + 1)),
        if StrictMono (t ∘ σ) then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0
      map_zero' := by funext t; simp
      map_add' := by
        intro s s'
        funext t
        simp only [Pi.add_apply, map_add, smul_add]
        simp only [ite_add_zero, Finset.sum_add_distrib] }

/-- The first sorting homotopy, given by its explicit junction sum.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechFirstSortingHom (p : ℕ) : S.cochains F (p + 1) ⟶ S.cochains F p := by
  classical
  exact AddCommGrpCat.ofHom
    { toFun := fun s t ↦ ∑ σ : Equiv.Perm (Fin (p + 1)),
        ∑ a : Fin (p + 1), ∑ τ : Equiv.Perm (Fin (p + 1)),
          if cechStableSort t σ ∧ cechPartialSort σ τ a then
            ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
              F.map (S.indexMap t (cechJunction σ τ a)).op
                (s (t ∘ cechJunction σ τ a)) else 0
      map_zero' := by funext t; simp
      map_add' := by
        intro s s'
        funext t
        simp only [Pi.add_apply, map_add, smul_add]
        simp only [ite_add_zero, Finset.sum_add_distrib] }

/-- Pull the repeated-tuple homotopy back by signed stable sorting.
Source: Stacks 01FM, equation 20.23.6.2.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechSecondSortingHom (p : ℕ) : S.cochains F (p + 1) ⟶ S.cochains F p := by
  classical
  exact AddCommGrpCat.ofHom
    { toFun := fun s t ↦ ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
        if cechStableSort t σ ∧ cechFirstRepeat (t ∘ σ) a then
          ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ a.val) •
            F.map (S.indexMap t (cechJunction σ σ a)).op
              (s (t ∘ cechJunction σ σ a)) else 0
      map_zero' := by funext t; simp
      map_add' := by
        intro s s'
        funext t
        simp only [Pi.add_apply, map_add, smul_add]
        simp only [ite_add_zero, Finset.sum_add_distrib] }

/-- Extend the first degree-lowering operator to the relevant pairs of degrees.
Source: Stacks 01FM; degree zero has no incoming component.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechFirstSortingFamily (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (S.complex F).X i ⟶ (S.complex F).X j :=
  eqToHom (congrArg (fun n ↦ S.cochains F n) h.symm) ≫ cechFirstSortingHom X U F S j

/-- Extend the second degree-lowering operator to the relevant pairs of degrees.
Source: Stacks 01FM; degree zero has no incoming component.
(blueprint: def-pc-alternating-cech-sorting-operators) -/
noncomputable def cechSecondSortingFamily (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (S.complex F).X i ⟶ (S.complex F).X j :=
  eqToHom (congrArg (fun n ↦ S.cochains F n) h.symm) ≫ cechSecondSortingHom X U F S j

end AlgebraicGeometry.Scheme
