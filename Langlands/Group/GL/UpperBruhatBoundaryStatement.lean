import Langlands.Group.GL.UpperBruhatFiltration
import Mathlib.Topology.Algebra.Field

/-! Strict inversion decrease on the boundaries of actual upper Bruhat cells. -/

namespace Langlands.GeneralLinear

universe u

/-- Over every Hausdorff topological field and in every rank, including zero, each
point of the closure of an actual upper triangular double coset `B * p * B` that lies
outside it belongs to an actual cell whose permutation has strictly fewer inversions.
The closure is taken in the existing units-of-matrices topology. -/
def UpperBruhatBoundaryStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
    closure (upperBruhatCell n K w) \ upperBruhatCell n K w ⊆
      {g | ∃ v : Equiv.Perm (Fin n),
        permutationInversionCount n v < permutationInversionCount n w ∧
        g ∈ upperBruhatCell n K v}

end Langlands.GeneralLinear
