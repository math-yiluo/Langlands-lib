/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Single

/-!
# Morphisms from/to single complexes

Supplement to `Mathlib.Algebra.Homology.Single`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

variable {V c}

/-- Morphisms `K ⟶ (single V c j).obj A` identify to morphisms `K.X j ⟶ A`
whose precomposition with `K.d i j` is zero, when `c.Rel i j`. -/
noncomputable def toSingleEquiv (A : V) (K : HomologicalComplex V c) (i j : ι) (hij : c.Rel i j) :
    (K ⟶ (single V c j).obj A) ≃ { f : K.X j ⟶ A // K.d i j ≫ f = 0 } where
  toFun f := ⟨f.f j ≫ (singleObjXSelf c j A).hom, by
    rw [← Hom.comm_assoc, single_obj_d, zero_comp, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f (fun k hk => by
    obtain rfl := (c.prev_eq' hij).symm.trans (c.prev_eq' hk)
    simpa using f.2)
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- Morphisms `(single V c i).obj A ⟶ K` identify to morphisms `A ⟶ K.X i`
whose postcomposition with `K.d i j` is zero, when `c.Rel i j`. -/
noncomputable def fromSingleEquiv (A : V) (K : HomologicalComplex V c) (i j : ι) (hij : c.Rel i j) :
    ((single V c i).obj A ⟶ K) ≃ { f : A ⟶ K.X i // f ≫ K.d i j = 0 } where
  toFun f := ⟨(singleObjXSelf c i A).inv ≫ f.f i, by simp⟩
  invFun f := HomologicalComplex.mkHomFromSingle f (fun k hk => by
    obtain rfl := (c.next_eq' hij).symm.trans (c.next_eq' hk)
    simpa using f.2)
  left_inv f := by aesop_cat
  right_inv f := by aesop_cat

end HomologicalComplex
