import Langlands.AllFieldBZ.Group.GL.MirabolicProjection
import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicCharacter
import Langlands.Representation.Derivative.TopLocalizationData

/-!
# All-field port of `Langlands.Representation.Derivative.TopLocalizationData`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.TopLocalizationData` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.TopLocalization
open Langlands.Derivative.TopLocalization hiding determinantNorm_upper realPowerCharacter_mirabolicUpper
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
universe uF

variable {F : Type uF} [Field F] {n : ℕ}

section Characters
variable (ψ : AddChar F ℂ)

variable [TopologicalSpace F] (χ : UnitaryAdditiveCharacter F)

end Characters
section Topology
variable [TopologicalSpace F]

end Topology
section Padic
variable {K : LocalFieldPackage.{uF}} (T : K.TopologicalData)

/-- The residue-normalized determinant norm is trivial on every full upper group. -/
theorem determinantNorm_upper (u : GeneralLinear.upperUnipotent n K.Carrier) :
    T.determinantNorm n u.val = 1 := by
  change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
  rw [determinant_upper, map_one]

/-- The exact determinant character used on the smaller mirabolic by `Φ⁻`
is trivial on its full upper-unipotent subgroup. -/
theorem realPowerCharacter_mirabolicUpper (s : ℝ)
    (u : Mirabolic.upperUnipotent n K.Carrier) :
    realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n K.Carrier).subtype)
      s u.val = 1 := by
  apply ker_le_realPowerCharacter_ker
  exact determinantNorm_upper T (upperUnipotentEquiv u)

end Padic
end Langlands.AllFieldBZ.Derivative.TopLocalization
