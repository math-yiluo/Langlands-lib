import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationProof
import Langlands.Group.GL.CountabilityProof

/-!
# All-field port of `Langlands.Group.GL.CountabilityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.CountabilityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u

variable {F : LocalFieldPackage.{u}}

/-- The supplied matrix-unit topology is sigma compact, including rank zero. -/
theorem generalLinearSigmaCompactSpace (T : F.TopologicalData) (n : ℕ) :
    let := T.generalLinearTopology n
    SigmaCompactSpace (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.generalLinearSecondCountableTopology n
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearLocallyCompactSpace n
  infer_instance

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

end Langlands.AllFieldBZ.LocalFieldPackage
