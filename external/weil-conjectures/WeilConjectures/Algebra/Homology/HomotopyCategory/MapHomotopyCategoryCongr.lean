/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # Equal functors induce equal functors on homotopy categories

Equal additive functors induce equal functors on homotopy categories
(`CategoryTheory.Functor.mapHomotopyCategory_congr`). This is useful when the equality of the
additive functors cannot be rewritten directly, because the `Additive` instances depend on it.
-/

@[expose] public section

namespace CategoryTheory.Functor

/-- Equal additive functors induce equal functors on homotopy categories. -/
lemma mapHomotopyCategory_congr {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] {ι : Type*} (c : ComplexShape ι) {F G : C ⥤ D} [F.Additive] [G.Additive]
    (h : F = G) : F.mapHomotopyCategory c = G.mapHomotopyCategory c := by
  subst h
  rfl

end CategoryTheory.Functor
