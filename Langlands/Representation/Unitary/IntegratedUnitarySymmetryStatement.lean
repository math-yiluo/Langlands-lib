import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

namespace Langlands.Analysis

open MeasureTheory
open scoped ENNReal NNReal

universe uG uE

/-- An actual inversion-density identity and the corresponding Hermitian weight
relation make the Bochner integrated unitary action symmetric. -/
def IntegratedUnitarySymmetryStatement : Prop :=
  ∀ {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) (π : G →* (E →L[ℂ] E))
    (hπinner : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)
    (d : G → ℝ≥0), Measurable d →
    μ.inv = μ.withDensity (fun g => (d g : ℝ≥0∞)) →
    ∀ (f : G → ℂ) (hf : Integrable f μ),
      (∀ᵐ g ∂μ, f g = (d g : ℂ) * star (f g⁻¹)) →
      let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
        fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
      (integratedIsometricAction μ π hπnorm hπmeas f hf).IsSymmetric

end Langlands.Analysis
