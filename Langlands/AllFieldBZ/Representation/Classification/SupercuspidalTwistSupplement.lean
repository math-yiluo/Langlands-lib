import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist

/-!
# All-field port of `norm_determinantPowerCharacter_scalar`

The norm of `|det|^s` at a scalar matrix, a declaration of the original module
`Langlands.Representation.Classification.SupercuspidalTwist` that is not part of its port
`Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist`, over an arbitrary
nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired
Markdown.
-/

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- `‖|det (z · 1_n)|^s‖ = |z|^(n s)` for the residue-normalized absolute value. -/
theorem norm_determinantPowerCharacter_scalar (n : ℕ) (s : ℝ)
    (z : F.Carrierˣ) :
    ‖(T.determinantPowerCharacter n s (GeneralLinear.scalar z) : ℂ)‖ =
      T.normalizedAbs z ^ ((n : ℝ) * s) := by
  rw [coe_realPowerCharacter, T.determinantNorm_scalar]
  change ‖(((T.normalizedAbs z ^ n) ^ s : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (pow_nonneg (T.normalizedAbs_nonneg _) _) _),
    ← Real.rpow_natCast_mul (T.normalizedAbs_nonneg _)]

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
