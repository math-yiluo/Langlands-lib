import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.Group.GL.Padic

/-!
# All-field port of `Langlands.Group.GL.Padic`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.Padic` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable {F : LocalFieldPackage.{u}}

namespace TopologicalData
/-- The matrix unit topology associated to a supplied realization of the field. -/
abbrev generalLinearTopology (T : F.TopologicalData) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact inferInstance

/-- Multiplication and inversion are continuous for the selected topology. -/
theorem generalLinearTopologicalGroup (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    IsTopologicalGroup (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact inferInstance

/-- The selected matrix unit topology is Hausdorff. -/
theorem generalLinearT2Space (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    T2Space (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.fieldT2
  exact inferInstance

/-- The selected matrix unit topology is locally compact. -/
theorem generalLinearLocallyCompactSpace (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    LocallyCompactSpace (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
  exact inferInstance

/-- The continuous determinant for the selected field realization. -/
def generalLinearDeterminant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier) F.Carrierˣ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.determinantContinuous

end TopologicalData
end Langlands.AllFieldBZ.LocalFieldPackage
