import Langlands.Group.GL.PadicBlocks
import Langlands.AllField.Group.GL.PadicBlocks
import Langlands.AllField.Group.GL.PadicSupplement
namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

variable {n : ℕ}

/-- The parabolic topology induced by the supplied field realization. -/
abbrev parabolicTopology (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.parabolic F) := by
  letI := T.topology
  infer_instance

/-- The parabolic is locally compact for this exact topology. -/
theorem parabolicLocallyCompactSpace (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    LocallyCompactSpace (B.parabolic F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.parabolicLocallyCompactSpace F

end LocalFieldData

end Langlands
