import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite-dimensional submodules preserved by the projections of a Hilbert sum -/

set_option autoImplicit false

namespace Langlands.Analysis

universe uIndex uSpace

/-- A finite-dimensional submodule preserved by the summand projections of an
internal Hilbert sum is the algebraic sum of its intersections with the summands.
At most its dimension many intersections are nonzero, and the same finite set
of indices gives the projection formula for every vector in the submodule. -/
def OrthogonalHilbertSumFiniteSubmoduleStatement : Prop :=
  ∀ (ι : Type uIndex) (E : Type uSpace) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E] (V : ι → Submodule ℂ E) [∀ i, CompleteSpace (V i)],
    IsHilbertSum ℂ (fun i => ↥(V i)) (fun i => (V i).subtypeₗᵢ) →
    ∀ (W : Submodule ℂ E) [FiniteDimensional ℂ W],
      (∀ i w, w ∈ W → (V i).starProjection w ∈ W) →
      ∃ s : Finset ι,
        (∀ i, i ∈ s ↔ W ⊓ V i ≠ ⊥) ∧
        s.card ≤ Module.finrank ℂ W ∧
        (∀ w ∈ W, ∑ i ∈ s, (V i).starProjection w = w) ∧
        W = ⨆ i, W ⊓ V i

end Langlands.Analysis
