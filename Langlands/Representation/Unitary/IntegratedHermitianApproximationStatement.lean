import Langlands.Representation.Unitary.HermitianWeightSequenceStatement
import Langlands.Representation.Unitary.IntegratedUnitarySymmetryStatement
import Langlands.Representation.Unitary.IntegratedIsometricApproximationStatement
import Langlands.Representation.Unitary.IntegratedIsometricNaturalityStatement

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

universe uG uE

/-- Continuous Hermitian weights yield actual symmetric contraction operators
converging strongly to the identity, with invariant-subspace naturality. -/
def IntegratedHermitianApproximationStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsCountablyGenerated (𝓝 (1 : G))]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (d : G →* ℝ≥0), Continuous d →
    μ.inv = μ.withDensity (fun g => (d g : ℝ≥0∞)) →
    ∀ (π : G →* (E →L[ℂ] E))
      (hπinner : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
      (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ),
      (∀ x : E, ContinuousAt (fun g => π g x) (1 : G)) →
      let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
        fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
      ∃ (f : ℕ → G → ℝ) (hf : ∀ n, Integrable (f n) μ),
        (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
          (∀ g, 0 ≤ f n g) ∧ (∫ g, f n g ∂μ) = 1 ∧
          ∀ g, f n g = (d g : ℝ) * f n g⁻¹) ∧
        (∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, tsupport (f n) ⊆ U) ∧
        let A := fun n => integratedIsometricAction μ π hπnorm hπmeas
          (fun g => (f n g : ℂ)) (hf n).ofReal
        (∀ n, (A n).IsSymmetric ∧ ‖A n‖ ≤ 1) ∧
        (∀ x : E, Tendsto (fun n => A n x) atTop (𝓝 x)) ∧
        ∀ (P : Submodule ℂ E) (_hPc : IsClosed (P : Set E))
          (hPi : ∀ (g : G) (x : E), x ∈ P → π g x ∈ P),
          ∃ hAP : ∀ n (x : E), x ∈ P → A n x ∈ P,
            ∀ (Q : Submodule ℂ E) (U : P ≃ₗᵢ[ℂ] Q),
              (∀ (g : G) (x : P),
                (U ⟨π g x, hPi g x x.property⟩ : E) = π g (U x : E)) →
              ∀ n (x : P), (U ⟨A n x, hAP n x x.property⟩ : E) = A n (U x : E)

end Langlands.Analysis
