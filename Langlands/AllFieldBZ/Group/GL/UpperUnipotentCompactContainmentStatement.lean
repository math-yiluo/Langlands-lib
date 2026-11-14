import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Group.GL.UpperUnipotentCompactContainmentStatement

/-!
# All-field port of `Langlands.Group.GL.UpperUnipotentCompactContainmentStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.UpperUnipotentCompactContainmentStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
universe uF

/-- Every compact subset of the actual upper-unipotent group lies in a compact
open subgroup, for each compatible p-adic topology and every rank. -/
def _root_.Langlands.GeneralLinear.UpperUnipotentCompactContainmentStatement_allFieldBZ : Prop :=
  ∀ (F : Langlands.AllFieldBZ.LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    ∀ C : Set (upperUnipotent n F.Carrier), IsCompact C →
      ∃ K : OpenSubgroup (upperUnipotent n F.Carrier),
        IsCompact (K : Set (upperUnipotent n F.Carrier)) ∧
        C ⊆ (K : Set (upperUnipotent n F.Carrier))

end Langlands.AllFieldBZ.GeneralLinear
