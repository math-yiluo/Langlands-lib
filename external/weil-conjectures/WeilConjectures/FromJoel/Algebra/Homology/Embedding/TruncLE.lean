/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation (≤): behaviour of `ιTruncLE` on degrees

Supplement to `Mathlib.Algebra.Homology.Embedding.TruncLE`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K : HomologicalComplex C c')
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [HasZeroObject C]

lemma isIso_ιTruncLE_f (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.ιTruncLE e).f (e.f i)) := by
  rw [← isIso_op_iff]
  exact K.op.isIso_πTruncGE_f e.op i hi

end HomologicalComplex
