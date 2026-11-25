/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact

Ported from the `proetale` package (`Proetale.Mathlib.Algebra.Homology.ShortComplex.Exact`).
-/

@[expose] public section

namespace CategoryTheory

open Limits

instance {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape WalkingParallelPair C] [HasColimitsOfShape WalkingParallelPair C] (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

lemma ShortComplex.exact_iff_evaluation {J : Type*} [Category J] {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C] [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C] (S : ShortComplex (J ⥤ C)) [S.HasHomology] :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  rw [exact_iff_isZero_homology, Functor.isZero_iff]
  refine forall_congr' fun j ↦ ?_
  let e : S.homology.obj j ≅ _ := (mapHomologyIso S ((evaluation J C).obj j)).symm
  rw [e.isZero_iff, exact_iff_isZero_homology]

end CategoryTheory
