import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.Group.GL.BlockIwahoriBasisStatement

/-!
# All-field port of `Langlands.Group.GL.BlockIwahoriBasisStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockIwahoriBasisStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open Filter
open Topology
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF

/-- Every identity neighborhood in the actual p-adic GL contains a compact open
subgroup with the published weak-chamber block Iwahori factorization. -/
def _root_.Langlands.GeneralLinear.BlockShape.BlockIwahoriBasisStatement_allFieldBZ {F : Langlands.AllFieldBZ.LocalFieldPackage.{uF}}
    {n : ℕ} (B : GeneralLinear.BlockShape n) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
    ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
      (K : Set (GeneralLinear n F.Carrier)) ⊆ U ∧
      B.HasBlockIwahoriFactorization_allFieldBZ T K

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
