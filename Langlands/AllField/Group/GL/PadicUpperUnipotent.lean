import Langlands.Group.GL.PadicUpperUnipotent
import Langlands.AllField.Group.GL.Padic
namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

/-- The full upper unipotent subgroup topology for the supplied realization. -/
abbrev upperUnipotentTopology (T : LocalFieldData F) (n : ℕ) :
    TopologicalSpace (GeneralLinear.upperUnipotent n F) := by
  letI := T.topology
  infer_instance

/-- The upper unipotent subgroup is Hausdorff. -/
theorem upperUnipotentT2Space (T : LocalFieldData F) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    T2Space (GeneralLinear.upperUnipotent n F) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The upper unipotent subgroup is locally compact by its proved closedness. -/
theorem upperUnipotentLocallyCompactSpace (T : LocalFieldData F) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    LocallyCompactSpace (GeneralLinear.upperUnipotent n F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact GeneralLinear.UpperUnipotent.locallyCompactSpace

end LocalFieldData

end Langlands
