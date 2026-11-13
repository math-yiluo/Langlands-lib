import Langlands.Representation.Derivative.MirabolicCharacter
import Langlands.AllField.Group.GL.Padic
/-! # The positive Bernstein–Zelevinsky character on the actual mirabolic radical -/

noncomputable section

namespace Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic
open Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative
open Langlands.AllField.Derivative

open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis

universe uF

variable {F : Type uF} [CommRing F]

variable [TopologicalSpace F]

end Langlands.AllField.Derivative.Mirabolic

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F]

/-- The BZ character for every supplied local-field topology. -/
def mirabolicTheta (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    radical (n + 1) F →* ℂˣ := by
  letI := T.topology
  exact Derivative.Mirabolic.theta ψ n

end Langlands.LocalFieldData
