import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.HarmonicAnalysis.RowFourierMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Row Fourier surjectivity under positive Haar scaling -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.HarmonicAnalysis

universe u

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]

/-- A constant scalar Haar rescaling contributes one factor per coordinate. -/
theorem rowMeasure_scale (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (c : NNReal) (hc : 0 < c) (d : ℕ) :
    rowMeasure (μ.scale c hc) d = (c : ℝ≥0∞) ^ d • rowMeasure μ d := by
  simpa using rowCoordinateMeasure_scale (fun _ : Fin d => μ)
    (fun _ => c) (fun _ => hc)

/-- Scaling the scalar Haar measure multiplies the actual row Fourier integral
by the dimension-th power of the scalar, including the empty product. -/
theorem rowFourierIntegral_scale (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (c : NNReal) (hc : 0 < c) (d : ℕ)
    (f : (Fin d → K) → ℂ) (y : Fin d → K) :
    rowFourierIntegral ψ (μ.scale c hc) d f y =
      ((c : ℝ) : ℂ) ^ d * rowFourierIntegral ψ μ d f y := by
  unfold rowFourierIntegral
  rw [rowMeasure_scale, integral_smul_measure]
  simp [ENNReal.toReal_pow, Complex.real_smul]

variable [LocallyCompactSpace K] [T2Space K] [SecondCountableTopology K]

/-- The exact published conditional Haar-normalization surjectivity target. -/
theorem rowFourierHaarSurjectivity
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (d : ℕ) :
    RowFourierHaarSurjectivityStatement K ψ μ d := by
  intro hclosed hself ν Φ
  have : SigmaFinite μ.measure := inferInstance
  let c : NNReal := Measure.addHaarScalarFactor ν.measure μ.measure
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hν : ν = μ.scale c hc := by
    apply AdditiveHaarMeasure.ext
    exact Measure.isAddLeftInvariant_eq_smul_of_regular ν.measure μ.measure
  let Φneg : SchwartzBruhat (Fin d → K) :=
    ⟨fun x => Φ (-x),
      Φ.locallyConstant.comp_continuous continuous_neg,
      Φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg _)⟩
  obtain ⟨g, hg⟩ := hclosed Φneg
  have hgfun : (g : (Fin d → K) → ℂ) = rowFourierIntegral ψ μ d Φneg :=
    funext hg
  have hFg : ∀ y, rowFourierIntegral ψ μ d g y = Φ y := by
    intro y
    rw [hgfun, (hself Φneg).2 y]
    simp [Φneg]
  let a : ℂ := ((c : ℝ) : ℂ) ^ d
  have ha : a ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
  refine ⟨a⁻¹ • g, ?_⟩
  intro y
  rw [hν, rowFourierIntegral_scale]
  change Φ y = a * rowFourierTransform ψ μ (a⁻¹ • g) y
  rw [map_smul]
  change Φ y = a * (a⁻¹ * rowFourierIntegral ψ μ d g y)
  rw [hFg y, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

end Langlands.HarmonicAnalysis
