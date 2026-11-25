/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation (≥): behaviour of `πTruncGE` on degrees

Supplement to `Mathlib.Algebra.Homology.Embedding.TruncGE`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K : HomologicalComplex C c')
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
lemma isIso_πTruncGE_f (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.πTruncGE e).f (e.f i)) := by
  dsimp [πTruncGE]
  rw [e.isIso_liftExtend_f_iff _ _ rfl,
    restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ rfl hi]
  infer_instance

end HomologicalComplex
