import Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
import Langlands.AllField.Group.GL.Padic
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding ParabolicQuotientCompactClause UnipotentFiniteContainmentClause
open Langlands.AllField.Parabolic

universe uF

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Compactness of the actual left quotient of a block parabolic. -/
def ParabolicQuotientCompactClause : Prop :=
  letI := T.topology
  CompactSpace (Induction.LeftQuotient (B.parabolic F))

/-- The finite-containment form used by the published smooth coinvariant target. -/
def UnipotentFiniteContainmentClause : Prop :=
  letI := T.topology
  ∀ s : Finset (B.unipotentRadical F),
    ∃ K : OpenSubgroup (B.unipotentRadical F),
      IsCompact (K : Set (B.unipotentRadical F)) ∧
      ∀ u ∈ s, u ∈ K

end Langlands.AllField.Parabolic
