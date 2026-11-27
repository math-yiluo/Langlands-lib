import Langlands.Geometry.Manifold.LinearLieGroup.Realization
import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Factorization of smooth vectors for a closed linear Lie group -/

open MeasureTheory Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Archimedean

universe uA uM uG uE

/-- The smooth-vector factorization of Dixmier and Malliavin for continuous complex
Banach representations of Lie groups with a closed linear realization. -/
def SmoothVectorFactorizationStatement : Prop :=
  ∀ (M : Type uM) [NormedAddCommGroup M] [NormedSpace ℝ M]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ChartedSpace M G] [MeasurableSpace G] [BorelSpace G]
    (A : Type uA) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [FiniteDimensional ℝ A] (j : G →* Aˣ),
    LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, M) j →
    ∀ (μ : Measure G) [μ.IsHaarMeasure]
      (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (π : G →* (E →L[ℂ] E)), IsContinuousRepresentation π →
      ∀ (U : Set G), U ∈ 𝓝 (1 : G) →
        ∀ v : E, IsSmoothVector 𝓘(ℝ, M) π v →
          ∃ (n : ℕ) (w : Fin n → E) (k : Fin n → G → ℂ),
            (∀ i, IsSmoothVector 𝓘(ℝ, M) π (w i) ∧
              ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, ℂ) ∞ (k i) ∧
              HasCompactSupport (k i) ∧ tsupport (k i) ⊆ U ∧
              Integrable (fun g => k i g • π g (w i)) μ) ∧
            v = ∑ i, ∫ g, k i g • π g (w i) ∂μ

end Langlands.Archimedean
