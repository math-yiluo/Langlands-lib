import Langlands.Group.GL.UpperBruhatCells
import Mathlib.Topology.Algebra.Field

/-! Local closedness of the actual upper Bruhat cells over Hausdorff topological fields. -/

namespace Langlands.GeneralLinear

universe u

/-- Every actual upper triangular double coset `B * p * B` is locally closed in the
existing units-of-matrices topology, over every Hausdorff topological field and in
every rank, including zero. -/
def UpperBruhatLocalClosednessStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
    IsLocallyClosed (upperBruhatCell n K w)

end Langlands.GeneralLinear
