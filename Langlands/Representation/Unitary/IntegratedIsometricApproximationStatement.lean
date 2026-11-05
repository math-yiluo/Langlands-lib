import Langlands.Representation.Unitary.IntegratedOperator

noncomputable section

namespace Langlands.Analysis

open MeasureTheory Filter
open scoped Topology

universe uG uE

/-- Normalized nonnegative weights concentrating at the identity give strong
convergence of the actual integrated operators. -/
def IntegratedIsometricApproximationStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) (π : G →* (E →L[ℂ] E))
    (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ),
    (∀ x : E, ContinuousAt (fun g => π g x) (1 : G)) →
    ∀ (f : ℕ → G → ℝ) (hf : ∀ n, Integrable (f n) μ),
      (∀ n g, 0 ≤ f n g) →
      (∀ n, ∫ g, f n g ∂μ = 1) →
      (∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, Function.support (f n) ⊆ U) →
      ∀ x : E, Tendsto
        (fun n => integratedIsometricAction μ π hπnorm hπmeas
          (fun g => (f n g : ℂ)) (hf n).ofReal x)
        atTop (𝓝 x)

end Langlands.Analysis
