import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Group.GL.Maps

/-!
# All-field port of `Langlands.Group.GL.Maps`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.Maps` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
universe u

variable (n : ℕ) (R : Type u) [CommRing R]

variable [TopologicalSpace R]

variable [IsTopologicalRing R]

end Langlands.AllFieldBZ.GeneralLinear
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable {F : LocalFieldPackage.{u}}

namespace TopologicalData
/-- Inverse transpose for the selected topology of a p-adic field. -/
def generalLinearInverseTranspose (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier := by
  letI := T.topology
  exact GeneralLinear.inverseTransposeContinuous n F.Carrier
