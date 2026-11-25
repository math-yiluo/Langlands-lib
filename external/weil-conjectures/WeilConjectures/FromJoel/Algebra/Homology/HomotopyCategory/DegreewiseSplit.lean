/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Degreewise split triangles are distinguished

Supplement to `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Preadditive

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace HomotopyCategory

lemma trianglehOfDegreewiseSplit_distinguished (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting) :
    CochainComplex.trianglehOfDegreewiseSplit S σ ∈ distTriang _ := by
  rw [distinguished_iff_iso_trianglehOfDegreewiseSplit]
  exact ⟨S, σ, ⟨Iso.refl _⟩⟩

end HomotopyCategory
