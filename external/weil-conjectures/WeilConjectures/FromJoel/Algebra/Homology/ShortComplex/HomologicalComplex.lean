/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The homology of homological complexes

Supplement to `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K : HomologicalComplex C c}

lemma Acyclic.of_iso (hK : K.Acyclic) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.Acyclic := by
  rw [acyclic_iff]
  exact fun n ↦ (hK n).of_iso e

end HomologicalComplex
