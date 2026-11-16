import Langlands.Global.RankinSelberg.UnequalGaugeReduction
import Langlands.Group.GL.LowerBlockLocalizationCoordinates

/-! # Determinant twists in rectangular Whittaker integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance rectangularGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rectangularGaugeRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

variable (F : Type u) [Field F] [NumberField F]

/-- The determinant-weighted nonnegative integral along the rectangular chart
and over the smaller Whittaker quotient. -/
def rectangularMellinIntegral {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : WhittakerQuotient F (t + 1),
      (∫⁻ x, Ξ (rectangularPoint F h p.out x)
        ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
        ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
    ∂whittakerQuotientMeasure F (t + 1)

/-- The determinant of the rectangular point is the determinant of its leading block. -/
theorem determinant_rectangularPoint {r t : ℕ} (h : t < r)
    (g : Points F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    AdelicGL.determinant F (r + 1)
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (rectangularPoint F h g x)) =
      AdelicGL.determinant F (t + 1)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) := by
  apply Units.ext
  simp only [rectangularPoint, MulEquiv.apply_symm_apply]
  change Matrix.det (Matrix.reindex _ _
    (GeneralLinear.lowerBlockLocalization 1
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) x 1).val) =
    Matrix.det (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g).val
  rw [Matrix.det_reindex_self, GeneralLinear.det_lowerBlockLocalization]
  simp

/-- The rectangular variable does not change the determinant norm. -/
theorem detNorm_rectangularPoint {r t : ℕ} (h : t < r)
    (g : Points F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    detNorm F (r + 1) (rectangularPoint F h g x) = detNorm F (t + 1) g := by
  rw [UnequalAnalytic.detNorm_eq_absDet, UnequalAnalytic.detNorm_eq_absDet]
  simp only [absDet, determinant_rectangularPoint]


/-- A determinant-twisted pointwise majorant bounds the rectangular Mellin
integral by the majorant at the shifted exponent. -/
theorem rectangularMellinIntegral_norm_le {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (Ξ : Points F (r + 1) → ℝ≥0∞) (β σ : ℝ)
    (hW : ∀ g : Points F (r + 1),
      ‖W g‖ₑ ≤ ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g) :
    rectangularMellinIntegral F h (fun g => ‖W g‖ₑ) σ ≤
      rectangularMellinIntegral F h Ξ (σ + β) := by
  unfold rectangularMellinIntegral
  calc
    _ ≤ ∫⁻ p : WhittakerQuotient F (t + 1),
        (ENNReal.ofReal (detNorm F (t + 1) p.out ^ β) *
          ∫⁻ x, Ξ (rectangularPoint F h p.out x)
            ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
          ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
      ∂whittakerQuotientMeasure F (t + 1) := by
        apply lintegral_mono
        intro p
        apply mul_le_mul_left
        calc
          _ ≤ ∫⁻ x, ENNReal.ofReal (detNorm F (t + 1) p.out ^ β) *
              Ξ (rectangularPoint F h p.out x)
            ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
              apply lintegral_mono
              intro x
              simpa only [detNorm_rectangularPoint] using hW (rectangularPoint F h p.out x)
          _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ p : WhittakerQuotient F (t + 1),
        (∫⁻ x, Ξ (rectangularPoint F h p.out x)
          ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
          ENNReal.ofReal (detNorm F (t + 1) p.out ^ (σ + β))
      ∂whittakerQuotientMeasure F (t + 1) := by
        congr 1
        funext p
        rw [Real.rpow_add (UnequalAnalytic.detNorm_pos F p.out),
          ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (UnequalAnalytic.detNorm_pos F p.out)) σ)]
        ac_rfl

/-- A determinant-twisted pointwise majorant transfers rectangular Mellin
convergence by adding its exponent to the outer exponent. -/
theorem rectangular_mellin_lt_top_of_majorant {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (Ξ : Points F (r + 1) → ℝ≥0∞) (β σ : ℝ)
    (hW : ∀ g : Points F (r + 1),
      ‖W g‖ₑ ≤ ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g)
    (hΞ :
      ∫⁻ p : WhittakerQuotient F (t + 1),
          (∫⁻ x, Ξ (rectangularPoint F h p.out x)
            ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
            ENNReal.ofReal (detNorm F (t + 1) p.out ^ (σ + β))
        ∂whittakerQuotientMeasure F (t + 1) < ⊤) :
    ∫⁻ p : WhittakerQuotient F (t + 1),
        (∫⁻ x, ‖W (rectangularPoint F h p.out x)‖ₑ
          ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
          ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
      ∂whittakerQuotientMeasure F (t + 1) < ⊤ := by
  exact lt_of_le_of_lt (rectangularMellinIntegral_norm_le F h W Ξ β σ hW) hΞ

end Langlands.Global.RankinSelbergGlobal
