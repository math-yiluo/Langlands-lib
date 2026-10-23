import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.Padic
import Mathlib.Topology.Algebra.OpenSubgroup

namespace Langlands.GeneralLinear

universe uF

/-- Every compact subset of the actual upper-unipotent group lies in a compact
open subgroup, for each compatible p-adic topology and every rank. -/
def UpperUnipotentCompactContainmentStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    ∀ C : Set (upperUnipotent n F.Carrier), IsCompact C →
      ∃ K : OpenSubgroup (upperUnipotent n F.Carrier),
        IsCompact (K : Set (upperUnipotent n F.Carrier)) ∧
        C ⊆ (K : Set (upperUnipotent n F.Carrier))

end Langlands.GeneralLinear
