import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Holomorphy of positive-weight Mellin integrals

The closed proposition below states an internal analytic consequence of
integrability at every positive real parameter. It supplies no proof.
-/

namespace Langlands.Analysis

open MeasureTheory

universe u

/-- Positive real weights and real-axis integrability imply holomorphy of the
actual complex-power Bochner integral on the positive half-plane. -/
def MellinHalfPlaneStatement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (c : X → ℂ) (d : X → ℝ) (κ : ℝ),
    (∀ x, 0 < d x) →
    AEStronglyMeasurable c μ →
    AEMeasurable d μ →
    (∀ t : ℝ, 0 < t →
      Integrable (fun x => c x * (d x : ℂ) ^ ((t : ℂ) - (κ : ℂ))) μ) →
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ x, c x * (d x : ℂ) ^ (s - (κ : ℂ)) ∂μ)
      {s : ℂ | 0 < s.re}

end Langlands.Analysis
