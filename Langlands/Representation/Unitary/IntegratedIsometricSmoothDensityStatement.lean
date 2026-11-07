import Langlands.Representation.Unitary.IntegratedOperator
import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

universe uV uG uE

namespace Langlands.Analysis

open MeasureTheory
open scoped Manifold ContDiff

/-- Smooth vectors are norm dense for the original strongly continuous
isometric action, using smooth inverse kernels on the original Lie group. -/
def IntegratedIsometricSmoothDensityStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [ChartedSpace V G] [LieGroup 𝓘(ℝ, V) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    [μ.IsMulLeftInvariant]
    (π : G →* (E →L[ℂ] E))
    (_hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (_hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ),
    (∀ x : E, Continuous (fun g => π g x)) →
      Dense (Langlands.Archimedean.smoothVectors 𝓘(ℝ, V) π : Set E)

end Langlands.Analysis
