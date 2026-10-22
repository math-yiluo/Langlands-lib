import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.CompactOpen

open Filter Topology

namespace Langlands.GeneralLinear.BlockShape

universe uF

/-- Every identity neighborhood in the actual p-adic GL contains a compact open
subgroup with the published weak-chamber block Iwahori factorization. -/
def BlockIwahoriBasisStatement {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {n : ℕ} (B : GeneralLinear.BlockShape n) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
    ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
      (K : Set (GeneralLinear n F.Carrier)) ⊆ U ∧
      B.HasBlockIwahoriFactorization T K

end Langlands.GeneralLinear.BlockShape
