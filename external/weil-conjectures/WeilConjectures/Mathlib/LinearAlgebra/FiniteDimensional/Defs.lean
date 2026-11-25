/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensional subspaces

A subspace `W` of a vector space over a division ring `K` is finite-dimensional if and only if it
is spanned by finitely many of its elements.
-/

@[expose] public section

namespace Submodule

/-- **Finite-dimensional subspaces.** A subspace `W` of a `K`-vector space is finite-dimensional
if and only if there are finitely many elements `v₁, …, vᵣ ∈ W` such that every element of `W` is
a `K`-linear combination of them.

(blueprint: `def-weil-finite-dimensional-subspace`) -/
theorem finiteDimensional_iff_exists_finset_span_eq {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (W : Submodule K V) :
    FiniteDimensional K W ↔ ∃ s : Finset V, ↑s ⊆ (W : Set V) ∧ span K (s : Set V) = W := by
  rw [← fg_iff_finiteDimensional]
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨s, hs ▸ subset_span, hs⟩, fun ⟨s, _, hs⟩ ↦ ⟨s, hs⟩⟩

end Submodule
