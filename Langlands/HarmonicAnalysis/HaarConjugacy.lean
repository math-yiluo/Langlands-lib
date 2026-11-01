import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Haar scaling under continuous group conjugacy -/

noncomputable section

namespace Langlands.Geometric

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

section HaarConjugacy

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]

/-- Continuous conjugacy preserves the actual Haar scaling character. -/
theorem haarChar_eq_of_conjugacy (e : G ≃ₜ* H) (a : G ≃ₜ* G) (b : H ≃ₜ* H)
    (h : ∀ g, e (a g) = b (e g)) :
    mulEquivHaarChar a = mulEquivHaarChar b := by
  let μ : Measure G := haar
  let ν : Measure H := μ.map e
  have : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  have : ν.Regular := Regular.map e.toHomeomorph
  have he : Measurable (e : G → H) := e.continuous.measurable
  have ha : Measurable (a : G → G) := a.continuous.measurable
  have hb : Measurable (b : H → H) := b.continuous.measurable
  have hcoord : b ∘ e = e ∘ a := funext fun g => (h g).symm
  have hscale : mulEquivHaarChar a • ν.map b = ν := by
    calc
      _ = (mulEquivHaarChar a • μ.map a).map e := by
        rw [Measure.map_smul _ he.aemeasurable]
        congr 1
        change (μ.map e).map b = (μ.map a).map e
        rw [Measure.map_map hb he, hcoord, ← Measure.map_map he ha]
      _ = ν := by rw [mulEquivHaarChar_smul_map μ a]
  symm
  rw [mulEquivHaarChar_eq ν]
  have hs := haarScalarFactor_smul (ν.map b) (ν.map b) (c := mulEquivHaarChar a)
  rw! [hscale] at hs
  simpa using hs

end HaarConjugacy

end Langlands.Geometric
