import Langlands.AllFieldBZ.Group.GL.MirabolicRadical
import Langlands.Representation.Derivative.MirabolicCharacter

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicCharacter`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicCharacter` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
universe uF

variable {F : Type uF} [CommRing F]

variable [TopologicalSpace F]

end Langlands.AllFieldBZ.Derivative.Mirabolic
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
universe uF

variable {F : LocalFieldPackage.{uF}}

/-- The BZ character for every supplied p-adic topological realization. -/
def mirabolicTheta (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    radical (n + 1) F.Carrier →* ℂˣ := by
  letI := T.topology
  exact Derivative.Mirabolic.theta ψ n

/-- The actual character kernel is open for every supplied p-adic topology. -/
theorem mirabolicTheta_isOpen_ker (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    IsOpen ((T.mirabolicTheta ψ n).ker : Set (radical (n + 1) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : NonarchimedeanGroup (GeneralLinear (n + 1 + 1) F.Carrier) :=
    valuativeGeneralLinearNonarchimedean F.Carrier (n + 1 + 1)
  exact Derivative.Mirabolic.theta_isOpen_ker ψ n

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
