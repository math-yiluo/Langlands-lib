/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.CosetCover

/-!
# Avoiding finitely many proper subspaces

A vector space over an infinite field is not the union of finitely many proper subspaces. This
is `Subspace.exists_eq_top_of_iUnion_eq_univ`, restated for an indexed family of proper
subspaces.
-/

@[expose] public section

namespace Subspace

variable {k V ι : Type*} [DivisionRing k] [Infinite k] [AddCommGroup V] [Module k V] [Finite ι]

/-- **Avoiding finitely many linear subspaces.** If `k` is an infinite field and
`W₁, …, Wₛ` are proper subspaces of a `k`-vector space `V`, then `V ≠ W₁ ∪ ⋯ ∪ Wₛ`.

Finite-dimensionality of `V`, assumed in the blueprint, is not needed.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem iUnion_ne_univ_of_ne_top {W : ι → Subspace k V} (hW : ∀ i, W i ≠ ⊤) :
    ⋃ i, (W i : Set V) ≠ Set.univ := fun h ↦
  (exists_eq_top_of_iUnion_eq_univ h).elim hW

end Subspace
