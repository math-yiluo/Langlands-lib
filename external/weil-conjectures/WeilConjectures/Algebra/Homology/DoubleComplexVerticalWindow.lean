/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Smart vertical interval truncations

Source: the interval construction in blueprint thm-sp-double-complex-spectral-sequences,
and Mathlib's canonical cochain-complex truncation functors.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace VerticalWindowAux

instance truncGE_preservesZero {I J : Type*} {c : ComplexShape I} {d : ComplexShape J}
    (e : c.Embedding d) [e.IsTruncGE] : (e.truncGEFunctor C).PreservesZeroMorphisms where
  map_zero K L := by
    change (e.extendFunctor C).map (HomologicalComplex.truncGE'Map (0 : K ⟶ L) e) = 0
    have h : HomologicalComplex.truncGE'Map (0 : K ⟶ L) e = 0 := by
      ext i
      by_cases hi : e.BoundaryGE i
      · simp [HomologicalComplex.truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
      · simp [HomologicalComplex.truncGE'Map_f_eq _ _ hi rfl]
    rw [h, Functor.map_zero]

instance truncLE_preservesZero {I J : Type*} {c : ComplexShape I} {d : ComplexShape J}
    (e : c.Embedding d) [e.IsTruncLE] : (e.truncLEFunctor C).PreservesZeroMorphisms where
  map_zero K L := by
    change (HomologicalComplex.unopFunctor C d.symm).map
      (HomologicalComplex.truncGEMap
        ((HomologicalComplex.opFunctor C d).map (0 : K ⟶ L).op) e.op).op = 0
    change (HomologicalComplex.unopFunctor C d.symm).map
      ((e.op.truncGEFunctor Cᵒᵖ).map
        ((HomologicalComplex.opFunctor C d).map (0 : K ⟶ L).op)).op = 0
    rw [op_zero, Functor.map_zero, Functor.map_zero, op_zero, Functor.map_zero]

end VerticalWindowAux

/-- Smart truncation of a nonnegative cochain complex to the interval `[a,b)`.
Extend by zero to the integers, truncate, and restrict back to nonnegative degrees.
Source: Mathlib's canonical truncation functors
(blueprint: def-sp-double-complex-vertical-window). -/
noncomputable def verticalWindow (a b : ℤ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  (ComplexShape.embeddingUpNat.extendFunctor C) ⋙
    (ComplexShape.embeddingUpIntGE a).truncGEFunctor C ⋙
    (ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C ⋙
    ComplexShape.embeddingUpNat.restrictionFunctor C

instance verticalWindow_preservesZero (a b : ℤ) :
    (verticalWindow (C := C) a b).PreservesZeroMorphisms := by
  unfold verticalWindow
  infer_instance

end HomologicalComplex₂
