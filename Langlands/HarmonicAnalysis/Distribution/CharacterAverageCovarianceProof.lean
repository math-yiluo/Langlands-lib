import Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Translation covariance of character-weighted product averaging

Substitute `(g₁, g₂) ↦ (a * g₁, g₂ * b)` in the defining integral. It preserves `μ.prod μ`
by left invariance on the first factor and right invariance on the second, and it turns the
inverse character weight into `χ a * χ b` times the weight at the translated point.
-/

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open MeasureTheory

universe uG uY

/-- Left translation by `a` in the first factor and right translation by `b` in the last
factor multiply the character average by `χ a * χ b`. -/
theorem characterAverageCovariance : CharacterAverageCovarianceStatement.{uG, uY} := by
  intro G Y _ _ _ _ _ _ χ μ _ _ _ _ a b α
  -- The substitution `(g₁, g₂) ↦ (a * g₁, g₂ * b)` preserves `μ.prod μ`.
  have hmp : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.mulLeft a) (MeasurableEquiv.mulRight b))
      (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_mul_left μ a).prod (measurePreserving_mul_right μ b)
  ext y
  change ∫ z : G × G, α (a * z.1, (y, z.2 * b)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) =
    ((χ a : ℂ) * (χ b : ℂ)) *
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
  rw [← hmp.integral_comp'
      (fun w : G × G => α (w.1, (y, w.2)) * ((χ w.1 : ℂ) * (χ w.2 : ℂ))⁻¹),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change α (a * z.1, (y, z.2 * b)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ =
    ((χ a : ℂ) * (χ b : ℂ)) *
      (α (a * z.1, (y, z.2 * b)) * ((χ (a * z.1) : ℂ) * (χ (z.2 * b) : ℂ))⁻¹)
  have ha : (χ a : ℂ) ≠ 0 := (χ a).ne_zero
  have hb : (χ b : ℂ) ≠ 0 := (χ b).ne_zero
  have h₁ : (χ z.1 : ℂ) ≠ 0 := (χ z.1).ne_zero
  have h₂ : (χ z.2 : ℂ) ≠ 0 := (χ z.2).ne_zero
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  field_simp

end Langlands.HarmonicAnalysis.SchwartzBruhat
