import Langlands.Group.GL.PadicOppositeBlocks
import Langlands.AllField.Group.GL.PadicBlocksSupplement
namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

variable {n : ℕ}

/-- The continuous actual lower-block projection into the common Levi. -/
def oppositeBlockLeviProjection (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.oppositeParabolic F) (B.Levi F) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.oppositeLeviProjectionContinuous F

end LocalFieldData

end Langlands
