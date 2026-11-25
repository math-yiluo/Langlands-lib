/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Complements on the hom complex

The type `CochainComplex.HomComplex.Triplet n` of pairs of integers `(p, q)` with
`p + n = q` is countable, since `p` determines `q`.
-/

@[expose] public section

namespace CochainComplex.HomComplex

instance (n : ℤ) : Countable (Triplet n) :=
  Function.Injective.countable (f := Triplet.p) fun ⟨_, _, h⟩ ⟨_, _, h'⟩ e ↦ by
    subst e h h'
    rfl

end CochainComplex.HomComplex
