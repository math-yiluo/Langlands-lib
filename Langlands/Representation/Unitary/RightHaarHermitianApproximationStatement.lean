import Langlands.Representation.Unitary.IntegratedHermitianApproximationStatement
import Langlands.Analysis.Local.HaarInversionDensityStatement

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

universe uG uE

/-- Actual right Haar measure and continuous unitary orbits yield a Hermitian
approximation by symmetric contractions, with invariant-subspace naturality. -/
def RightHaarHermitianApproximationStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [IsHaarMeasure μ]
    (π : G →* (E →L[ℂ] E))
    (hπinner : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hπcont : ∀ x : E, Continuous (fun g => π g x)),
    let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
      fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
    let hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ.inv :=
      fun x => (hπcont x).stronglyMeasurable.aestronglyMeasurable
    ∃ (f : ℕ → G → ℝ) (hf : ∀ n, Integrable (f n) μ.inv),
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
        (∀ g, 0 ≤ f n g) ∧ (∫ g, f n g ∂μ.inv) = 1 ∧
        ∀ g, f n g = (modularCharacter g⁻¹ : ℝ) * f n g⁻¹) ∧
      (∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, tsupport (f n) ⊆ U) ∧
      let A := fun n => integratedIsometricAction μ.inv π hπnorm hπmeas
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
