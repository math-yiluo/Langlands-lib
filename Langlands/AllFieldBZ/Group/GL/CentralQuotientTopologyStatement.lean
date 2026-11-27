import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Group.GL.CentralQuotientTopologyStatement

/-!
# All-field port of `Langlands.Group.GL.CentralQuotientTopologyStatement`

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ

universe uG uF

/-- Every actual general linear group and product Levi has a locally compact,
Hausdorff, second-countable full central quotient, with sigma-finite Haar
measures for every Borel realization. -/
def GLBlockCentralQuotientTopologyStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ),
      Langlands.CentralQuotientHaarTopology (GeneralLinear n F.Carrier) ∧
      ∀ B : GeneralLinear.BlockShape n,
        letI := T.leviTopology B
        Langlands.CentralQuotientHaarTopology (B.Levi F.Carrier)

end Langlands.AllFieldBZ
