import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Transport of densities by measurable maps -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Langlands.RankinSelberg.GLDeterminantDensity

section Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Push a pulled-back density through a measurable embedding. -/
theorem map_withDensity_comp (μ : Measure X) {e : X → Y}
    (he : MeasurableEmbedding e) (w : Y → ℝ≥0∞) :
    (μ.withDensity (fun x => w (e x))).map e = (μ.map e).withDensity w := by
  ext s hs
  rw [he.map_apply, withDensity_apply _ (he.measurable hs), withDensity_apply _ hs,
    he.restrict_map, he.lintegral_map]

/-- Transport a density through a measurable equivalence. -/
theorem map_withDensity_equiv (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ℝ≥0∞) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  convert map_withDensity_comp μ e.measurableEmbedding (fun y => w (e.symm y)) using 1
  simp only [e.symm_apply_apply]

end Measure

end Langlands.RankinSelberg.GLDeterminantDensity
