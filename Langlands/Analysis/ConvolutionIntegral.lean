import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The left-Haar convolution integral of two complex functions on a group -/

noncomputable section

open MeasureTheory

namespace Langlands.Hecke

universe u

variable {G : Type u} [Group G] [MeasurableSpace G]

/-- Left-Haar convolution, with the convention `f(y) g(y⁻¹x)`.
For arbitrary functions this uses the usual Bochner integral convention. -/
def convolutionIntegral (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

end Langlands.Hecke
