import Langlands.Group.GL.Padic
import Langlands.AllField.LocalField.Foundation
/-!
# General linear groups over every nonarchimedean local field

These explicit structures install the topology of supplied local-field data
`T : LocalFieldData F` on the actual matrix unit group.
-/

namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

/-- The matrix unit topology associated to a supplied realization of the field. -/
abbrev generalLinearTopology (T : LocalFieldData F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F) := by
  letI := T.topology
  exact inferInstance

/-- Multiplication and inversion are continuous for the selected topology. -/
theorem generalLinearTopologicalGroup (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    IsTopologicalGroup (GeneralLinear n F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact inferInstance

/-- The selected matrix unit topology is Hausdorff. -/
theorem generalLinearT2Space (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    T2Space (GeneralLinear n F) := by
  let := T.topology
  let := T.fieldT2
  exact inferInstance

/-- The selected matrix unit topology is locally compact. -/
theorem generalLinearLocallyCompactSpace (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    LocallyCompactSpace (GeneralLinear n F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  exact inferInstance

/-- The continuous determinant for the selected field realization. -/
def generalLinearDeterminant (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F) Fˣ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.determinantContinuous

end LocalFieldData

end Langlands
