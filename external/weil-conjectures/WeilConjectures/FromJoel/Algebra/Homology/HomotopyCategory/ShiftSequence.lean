/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Shift functors preserve quasi-isomorphisms

Supplement to `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

open HomologicalComplex

variable (C : Type*) [Category* C] [Preadditive C] [CategoryWithHomology C]

lemma preservesQuasiIso_shiftFunctor (n : ℤ) :
    preservesQuasiIso (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) := by
  rintro _ _ _ hf
  simp only [mem_quasiIso_iff, MorphismProperty.inverseImage_iff] at hf ⊢
  infer_instance

end CochainComplex
