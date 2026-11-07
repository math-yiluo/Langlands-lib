import Langlands.Representation.Unitary.IntegratedOperator
import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

universe uV uG uE

namespace Langlands.Analysis

open MeasureTheory
open scoped Manifold ContDiff

/-- An actual integrated vector for an inverse smooth compact kernel belongs to
the original representation's existing subspace of smooth vectors. -/
def IntegratedIsometricSmoothVectorsStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [ChartedSpace V G]
    [LieGroup 𝓘(ℝ, V) ∞ G] [MeasurableSpace G] [BorelSpace G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (π : G →* (E →L[ℂ] E))
    (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ),
    (∀ x : E, Continuous (fun g => π g x)) →
    ∀ κ : G → ℂ,
      ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) ∞ κ → HasCompactSupport κ →
      Integrable (fun g => κ g⁻¹) μ ∧
        ∀ (hκinv : Integrable (fun g => κ g⁻¹) μ) (x : E),
          integratedIsometricAction μ π hπnorm hπmeas
            (fun g => κ g⁻¹) hκinv x ∈
              Langlands.Archimedean.smoothVectors 𝓘(ℝ, V) π

end Langlands.Analysis
