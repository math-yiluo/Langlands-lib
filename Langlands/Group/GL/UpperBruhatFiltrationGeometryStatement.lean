import Langlands.Group.GL.UpperBruhatFiltration
import Mathlib.Topology.Algebra.Field

/-!
# Closed inversion layers and open neighborhoods of actual upper Bruhat cells
-/

namespace Langlands.GeneralLinear

universe u

/-- Over every Hausdorff topological field and in every rank, including zero, in the
existing units-of-matrices topology: every inversion layer of the actual upper Bruhat
cells is closed, every union of strictly higher cells and every cell neighborhood
`C_w ∪ upperBruhatHigherCells n K w` is open, and every cell `C_w` is closed in its
neighborhood for the inherited subtype topology. -/
def UpperBruhatFiltrationGeometryStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ),
    (∀ k : ℕ, IsClosed (upperBruhatLayerLE n K k)) ∧
      (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatHigherCells n K w)) ∧
      (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatCellNeighborhood n K w)) ∧
      ∀ w : Equiv.Perm (Fin n),
        IsClosed {g : upperBruhatCellNeighborhood n K w | g.val ∈ upperBruhatCell n K w}

end Langlands.GeneralLinear
