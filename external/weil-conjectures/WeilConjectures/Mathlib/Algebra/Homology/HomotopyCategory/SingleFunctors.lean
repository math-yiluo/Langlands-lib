/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Additive functors and the single functors to cochain complexes

The isomorphisms `F(A[a]) ≅ F(A)[a]` (`HomologicalComplex.singleMapHomologicalComplex`) are
compatible with the shifts of the single functors.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]

/-- The isomorphisms `F(A[a]) ≅ F(A)[a]` are compatible with the shift isomorphisms of the single
functors. -/
lemma mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app (n a a' : ℤ) (h : n + a = a')
    (A : C) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso n a a' h).hom.app A) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a).hom.app A =
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app
        ((HomologicalComplex.single C (.up ℤ) a').obj A) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a').hom.app A)⟦n⟧' ≫
      ((CochainComplex.singleFunctors D).shiftIso n a a' h).hom.app (F.obj A) := by
  ext i
  by_cases hi : i = a
  · subst hi
    obtain rfl : a' = i + n := by lia
    simp [CochainComplex.singleFunctors, HomologicalComplex.singleMapHomologicalComplex,
      eqToHom_map]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

end CategoryTheory.Functor
