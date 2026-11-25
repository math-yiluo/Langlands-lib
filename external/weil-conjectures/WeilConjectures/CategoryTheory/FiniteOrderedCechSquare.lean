/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.CompleteLattice.Basic
import WeilConjectures.CategoryTheory.AlternatingCofaceSquare

/-! # The ordered finite Cech differential

Source: Stacks Project, Cohomology of Sheaves, Tag 01FJ. A contravariant coefficient
functor on a complete lattice gives an ordered Cech differential on the biproducts
indexed by increasing tuples. Double deletions agree by functoriality and their
signs cancel.
(blueprint: new-finite-cover-ordered-cech-square)
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uL uC vC

variable {L : Type uL} [CompleteLattice L] {C : Type uC} [Category.{vC} C]
  [Preadditive C] (F : Lᵒᵖ ⥤ C) {m : ℕ} (U : Fin m → L)
  (hB : ∀ p : ℕ, HasBiproduct
    (fun a : Fin (p + 1) ↪o Fin m ↦ F.obj (op (⨅ k, U (a k)))))

/-- The ordered Cech terms of a contravariant coefficient functor.
Source: Stacks Project, Tag 01FJ.
(blueprint: new-finite-cover-ordered-cech-square) -/
def finiteOrderedCechTerm (p : ℕ) : C := by
  letI := hB p
  exact ⨁ (fun a : Fin (p + 1) ↪o Fin m ↦ F.obj (op (⨅ k, U (a k))))

/-- One deletion coface on ordered Cech terms.
Source: Stacks Project, Tag 01FJ.
(blueprint: new-finite-cover-ordered-cech-square) -/
def finiteOrderedCechCoface (p : ℕ) (j : Fin (p + 2)) :
    finiteOrderedCechTerm F U hB p ⟶ finiteOrderedCechTerm F U hB (p + 1) := by
  letI := hB p
  letI := hB (p + 1)
  exact biproduct.lift (fun a : Fin (p + 2) ↪o Fin m ↦
    biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦ F.obj (op (⨅ k, U (b k))))
      (j.succAboveOrderEmb.trans a) ≫
        F.map (homOfLE (le_iInf fun k ↦
          iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op)

/-- The double-deletion identity on ordered Cech cofaces.
Source: Stacks Project, Tag 01FJ. Project onto a final increasing tuple. Both
composites first project onto that tuple with two entries deleted and then
restrict along the same inclusion of intersections. The simplex identity
identifies the deleted tuple; the source lattice is a thin category, so the
inclusions agree.
(blueprint: new-finite-cover-ordered-cech-square) -/
theorem finiteOrderedCechCoface_comp (p : ℕ) (i : Fin (p + 2))
    (j : Fin (p + 3)) (h : j.val ≤ i.val) :
    finiteOrderedCechCoface F U hB p i ≫ finiteOrderedCechCoface F U hB (p + 1) j =
      finiteOrderedCechCoface F U hB p
        (j.castLT (lt_of_le_of_lt h i.is_lt)) ≫
          finiteOrderedCechCoface F U hB (p + 1) i.succ := by
  let := hB p
  let := hB (p + 1)
  let := hB (p + 2)
  apply biproduct.hom_ext
  intro a
  simp only [finiteOrderedCechCoface, Category.assoc, biproduct.lift_π,
    biproduct.lift_π_assoc, ← F.map_comp]
  have he : i.succAboveOrderEmb.trans (j.succAboveOrderEmb.trans a) =
      (j.castLT (lt_of_le_of_lt h i.is_lt)).succAboveOrderEmb.trans
        (i.succ.succAboveOrderEmb.trans a) := by
    apply DFunLike.ext
    intro k
    simpa [SimplexCategory.δ] using congrArg
      (fun θ : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + 2) ↦
      a (θ.toOrderHom k)) (SimplexCategory.δ_comp_δ'' (show j ≤ i.castSucc from h)).symm
  classical
  let Φ (b : Fin (p + 1) ↪o Fin m) :
      finiteOrderedCechTerm F U hB p ⟶ F.obj (op (⨅ k, U (a k))) :=
    if h : (⨅ k, U (a k)) ≤ ⨅ k, U (b k) then
      biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦ F.obj (op (⨅ k, U (b k)))) b ≫
        F.map (homOfLE h).op
    else 0
  have h₁ : (⨅ k, U (a k)) ≤
      ⨅ k, U ((i.succAboveOrderEmb.trans (j.succAboveOrderEmb.trans a)) k) :=
    le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove (i.succAbove k))
  have h₂ : (⨅ k, U (a k)) ≤
      ⨅ k, U (((j.castLT (lt_of_le_of_lt h i.is_lt)).succAboveOrderEmb.trans
        (i.succ.succAboveOrderEmb.trans a)) k) :=
    le_iInf fun k ↦ iInf_le (fun l ↦ U (a l))
      (i.succ.succAbove ((j.castLT (lt_of_le_of_lt h i.is_lt)).succAbove k))
  simpa only [Φ, dite_eq_left h₁, dite_eq_left h₂, ← op_comp, homOfLE_comp] using congrArg Φ he

/-- The signed ordered Cech differential squares to zero.
Source: Stacks Project, Tag 01FJ. The preceding double-deletion identity gives the
hypothesis of `alternatingCofaceSquare`.
(blueprint: new-finite-cover-ordered-cech-square) -/
theorem finiteOrderedCechDifferential_squared (p : ℕ) :
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • finiteOrderedCechCoface F U hB p i) ≫
      (∑ j : Fin (p + 3), (-1 : ℤ) ^ (j : ℕ) •
        finiteOrderedCechCoface F U hB (p + 1) j) = 0 := by
  exact alternatingCofaceSquare (finiteOrderedCechTerm F U hB)
    (finiteOrderedCechCoface F U hB) (finiteOrderedCechCoface_comp F U hB) p

end CategoryTheory
