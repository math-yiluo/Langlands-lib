import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Representation.Parabolic.GeometricPrerequisitesStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.GeometricPrerequisitesStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.GeometricPrerequisitesStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding ParabolicQuotientCompactClause UnipotentFiniteContainmentClause
universe uF

variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Compactness of the actual left quotient of a block parabolic. -/
def ParabolicQuotientCompactClause : Prop :=
  letI := T.topology
  CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier))

/-- The finite-containment form used by the published smooth coinvariant target. -/
def UnipotentFiniteContainmentClause : Prop :=
  letI := T.topology
  ∀ s : Finset (B.unipotentRadical F.Carrier),
    ∃ K : OpenSubgroup (B.unipotentRadical F.Carrier),
      IsCompact (K : Set (B.unipotentRadical F.Carrier)) ∧
      ∀ u ∈ s, u ∈ K

end Langlands.AllFieldBZ.Parabolic
