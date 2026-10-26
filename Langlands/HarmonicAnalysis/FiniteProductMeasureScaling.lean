import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal ENNReal

namespace Langlands.HarmonicAnalysis

theorem pi_nnreal_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi]
  exact (Finset.prod_smul _ _ _).symm

end Langlands.HarmonicAnalysis
