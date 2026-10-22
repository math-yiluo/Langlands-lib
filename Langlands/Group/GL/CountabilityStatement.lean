import Langlands.Group.GL.PadicBlocks

/-! Countability properties for actual p-adic matrix groups. -/

namespace Langlands.PadicField

universe u

/-- Actual general linear groups and their block parabolics are second countable
and sigma compact for every supplied compatible field topology. -/
def MatrixGroupCountabilityTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    (SecondCountableTopology (GeneralLinear n F.Carrier) ∧
      SigmaCompactSpace (GeneralLinear n F.Carrier)) ∧
    ∀ B : GeneralLinear.BlockShape n,
      SecondCountableTopology (B.parabolic F.Carrier) ∧
        SigmaCompactSpace (B.parabolic F.Carrier)

end Langlands.PadicField
