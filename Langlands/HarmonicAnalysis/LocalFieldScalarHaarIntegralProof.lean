import Langlands.HarmonicAnalysis.LocalFieldScalarHaarIntegralStatement
import Langlands.BaseChange.WeylHaarScaling

/-! # Scalar change of variables for local-field Haar integrals -/

open MeasureTheory
open scoped NNReal

namespace Langlands.HarmonicAnalysis

universe u

theorem localFieldScalarHaarIntegral (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    LocalFieldScalarHaarIntegralStatement F := by
  intro _ _ μ _ a f
  have ha : Measurable (fun x : F => (a : F) * x) := (continuous_const.mul continuous_id).measurable
  rw [← integral_map_of_stronglyMeasurable ha f.continuous.stronglyMeasurable,
    BaseChange.map_mul_residueAbsolute F μ (a : F) a.ne_zero, integral_smul_nnreal_measure]
  change (((BaseChange.residueAbsoluteNNReal F (a : F))⁻¹ : ℝ≥0) : ℝ) • (∫ x, f x ∂μ) = _
  rw [NNReal.coe_inv]
  rfl

end Langlands.HarmonicAnalysis
