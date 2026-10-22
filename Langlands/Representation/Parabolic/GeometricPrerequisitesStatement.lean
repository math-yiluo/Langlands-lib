import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic
import Langlands.Representation.Induction.Definitions

namespace Langlands.Parabolic

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Compactness of the actual left quotient of a block parabolic. -/
def ParabolicQuotientCompactClause : Prop :=
  letI := T.topology
  CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier))

/-- A nested compact-open exhaustion of the actual unipotent radical. -/
def UnipotentExhaustionClause : Prop :=
  letI := T.topology
  ∃ K : ℕ → OpenSubgroup (B.unipotentRadical F.Carrier),
    (∀ i, IsCompact (K i : Set (B.unipotentRadical F.Carrier))) ∧
    Monotone (fun i => (K i).toSubgroup) ∧
    ∀ u : B.unipotentRadical F.Carrier, ∃ i, u ∈ K i

/-- The finite-containment form used by the published smooth coinvariant target. -/
def UnipotentFiniteContainmentClause : Prop :=
  letI := T.topology
  ∀ s : Finset (B.unipotentRadical F.Carrier),
    ∃ K : OpenSubgroup (B.unipotentRadical F.Carrier),
      IsCompact (K : Set (B.unipotentRadical F.Carrier)) ∧
      ∀ u ∈ s, u ∈ K

/-- Geometric hypotheses of the structural arguments, stated for actual groups
as proof obligations rather than fields of group data. -/
def GeometricPrerequisitesStatement : Prop :=
  ParabolicQuotientCompactClause F T B ∧
  UnipotentExhaustionClause F T B ∧
  UnipotentFiniteContainmentClause F T B

end Langlands.Parabolic
