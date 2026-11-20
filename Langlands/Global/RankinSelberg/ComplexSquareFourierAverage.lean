import Langlands.Global.RankinSelberg.ComplexSquareFourierMarginal

/-! # Fourier integrals of compact averages of square matrix tests -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier

open ArchimedeanLocal Langlands.LocalFactor.Archimedean Langlands.RankinSelberg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The product of the complex self-dual measure in all entries of a square matrix. -/
abbrev squareSelfDualMeasure (n : ℕ) (a : ℂˣ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  rectangularMeasure (complexSelfDualMeasure a) n n

/-- Jacquet's matrix Fourier integral, expressed on a raw matrix function. -/
def squareFourierIntegral (a : ℂˣ) (f : Mat → ℂ) (X : Mat) : ℂ :=
  ∫ Y, f Y * (complexScaledCharacter a).complex (-Matrix.trace (Xᵀ * Y))
    ∂squareSelfDualMeasure n a

theorem matrixTransform_eq_squareFourierIntegral (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    matrixTransform a Φ X = squareFourierIntegral a Φ X := matrixTransform_apply a Φ X

/-- A compact average of measure-preserving matrix pullbacks can be moved through the
Fourier integral. The two Schwartz tests specify the original test and its average. -/
def ComplexSquareFourierAverageStatement : Prop :=
  ∀ {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (κ : Measure K) [IsFiniteMeasure κ] (a : ℂˣ) (w : K → ℂ) (T : K → Mat → Mat),
    Continuous w → Continuous (Function.uncurry T) →
    (∀ k, MeasurePreserving (T k) (squareSelfDualMeasure n a) (squareSelfDualMeasure n a)) →
    ∀ (Φ Ψ : 𝓢(Mat, ℂ)), (∀ Y, Ψ Y = ∫ k, w k * Φ (T k Y) ∂κ) → ∀ X,
      matrixTransform a Ψ X = ∫ k, w k * squareFourierIntegral a (Φ ∘ T k) X ∂κ

theorem complexSquareFourierAverage : ComplexSquareFourierAverageStatement (n := n) := by
  intro K _ _ _ _ κ _ a w T hw hT hpres Φ Ψ hΨ X
  let μ := squareSelfDualMeasure n a
  have : SigmaFinite (complexSelfDualMeasure a).measure := by
    rw [ComplexTraceFourier.measure_eq]
    infer_instance
  have : μ.IsAddHaarMeasure := rectangularMeasure_isAddHaar (complexSelfDualMeasure a) n n
  have : SigmaFinite μ := rectangularMeasure_sigmaFinite (complexSelfDualMeasure a) n n
  let χ (Y : Mat) := (complexScaledCharacter a).complex (-Matrix.trace (Xᵀ * Y))
  have hχ : Continuous χ := (complexScaledCharacter a).continuous_complex.comp
    ((continuous_const.matrix_mul continuous_id).matrix_trace.neg)
  have hnorm (Y : Mat) : ‖χ Y‖ = 1 := (complexScaledCharacter a).norm_complex _
  have hΦ : Integrable Φ μ := Φ.integrable
  let f (k : K) (Y : Mat) := w k * Φ (T k Y) * χ Y
  have hf : Continuous (Function.uncurry f) :=
    ((hw.comp continuous_fst).mul (Φ.continuous.comp hT)).mul (hχ.comp continuous_snd)
  have hI : Integrable (Function.uncurry f) (κ.prod μ) := by
    refine (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨ae_of_all _ ?_, ?_⟩
    · intro k
      exact (((hpres k).integrable_comp_of_integrable hΦ).const_mul (w k)).mul_bdd
        hχ.aestronglyMeasurable (ae_of_all _ fun Y => (hnorm Y).le)
    have hi (k : K) : (∫ Y, ‖f k Y‖ ∂μ) = ‖w k‖ * ∫ Y, ‖Φ Y‖ ∂μ := by
      simp only [f, norm_mul, hnorm, mul_one, integral_const_mul]
      rw [← integral_map (hpres k).measurable.aemeasurable Φ.continuous.norm.aestronglyMeasurable,
        (hpres k).map_eq]
    simpa only [Function.uncurry_apply_pair, hi] using
      (hw.norm.integrable_of_hasCompactSupport (μ := κ)
        (HasCompactSupport.of_compactSpace _)).mul_const (∫ Y, ‖Φ Y‖ ∂μ)
  rw [matrixTransform_eq_squareFourierIntegral, squareFourierIntegral]
  calc
    (∫ Y, Ψ Y * χ Y ∂μ) = ∫ Y, (∫ k, f k Y ∂κ) ∂μ := by
      simp_rw [hΨ, f, integral_mul_const]
    _ = ∫ k, (∫ Y, f k Y ∂μ) ∂κ := (integral_integral_swap hI).symm
    _ = _ := by
      simp only [f, mul_assoc, integral_const_mul, squareFourierIntegral, Function.comp_apply]
      rfl

end Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier
