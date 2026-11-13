import Langlands.Group.GL.CountabilityProof
import Langlands.AllField.Group.GL.PadicBlocks
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
/-! Countability certificates for actual local-field general linear groups and parabolics. -/

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe u

variable {F : Type u} [Field F]

/-- The supplied matrix-unit topology is sigma compact, including rank zero. -/
theorem generalLinearSigmaCompactSpace (T : LocalFieldData F) (n : ℕ) :
    let := T.generalLinearTopology n
    SigmaCompactSpace (GeneralLinear n F) := by
  let := T.topology
  let := T.generalLinearSecondCountableTopology n
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearLocallyCompactSpace n
  infer_instance

end Langlands.LocalFieldData

namespace Langlands

universe u

end Langlands
