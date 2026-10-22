import Langlands.Group.GL.CountabilityStatement
import Langlands.Representation.Smooth.SmallRealizationProof

/-! Countability certificates for actual p-adic general linear groups and parabolics. -/

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

/-- The supplied matrix-unit topology is sigma compact, including rank zero. -/
theorem generalLinearSigmaCompactSpace (T : F.TopologicalData) (n : ℕ) :
    let := T.generalLinearTopology n
    SigmaCompactSpace (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.generalLinearSecondCountableTopology n
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearLocallyCompactSpace n
  infer_instance

/-- The actual block parabolic is second countable in the supplied topology. -/
theorem parabolicSecondCountableTopology (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    let := T.parabolicTopology B
    SecondCountableTopology (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.generalLinearSecondCountableTopology n
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The actual block parabolic is sigma compact in the supplied topology. -/
theorem parabolicSigmaCompactSpace (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    let := T.parabolicTopology B
    SigmaCompactSpace (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.parabolicSecondCountableTopology B
  let := T.parabolicTopologicalGroup B
  let := T.parabolicLocallyCompactSpace B
  infer_instance

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe u

/-- The exact grouped countability proposition for all supplied realizations. -/
theorem matrixGroupCountability : MatrixGroupCountabilityTheorem.{u} := by
  intro p _ F T n
  exact ⟨⟨T.generalLinearSecondCountableTopology n, T.generalLinearSigmaCompactSpace n⟩,
    fun B => ⟨T.parabolicSecondCountableTopology B, T.parabolicSigmaCompactSpace B⟩⟩

end Langlands.PadicField
