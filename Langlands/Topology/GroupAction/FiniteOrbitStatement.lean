import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.SigmaCompact

/-! Finite orbit ordering for sigma-compact topological group actions. -/

namespace Langlands.Topology

universe uH uX

/-- The orbits of a continuous sigma-compact group action on a locally compact
Hausdorff space admit a finite ordering with open initial unions. -/
def FiniteOrbitOrdering : Prop :=
  ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SigmaCompactSpace H] (X : Type uX) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [MulAction H X] [ContinuousSMul H X],
    Finite (MulAction.orbitRel.Quotient H X) →
    ∃ (n : ℕ) (r : Fin n → X),
      (∀ x : X, ∃ i, x ∈ MulAction.orbit H (r i)) ∧
      Pairwise (fun i j => Disjoint (MulAction.orbit H (r i))
        (MulAction.orbit H (r j))) ∧
      ∀ k : Fin (n + 1), IsOpen
        {x : X | ∃ i : Fin n, i.val < k.val ∧ x ∈ MulAction.orbit H (r i)}

end Langlands.Topology
