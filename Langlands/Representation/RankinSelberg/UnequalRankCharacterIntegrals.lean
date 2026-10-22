import Langlands.Representation.RankinSelberg.UnequalRankCharacterTransport

/-!
# Conditional unequal-rank integral transport
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory
open scoped NNReal ENNReal

universe uF

variable {F : Type uF} [Field F]

/-- Positive exponent for the pushforward of row scaling on j by (n+1) matrices. -/
def characterChangeRectangularExponent (j n : ℕ) : ℕ :=
  (n + 1) * ∑ i : Fin j, (i.val + 1)

/-- Expected pushforward multiplier for the inverse powers in the row scaling. -/
def characterChangeRectangularModulus (abv : AbsoluteValue F ℝ) (a : Fˣ) (j n : ℕ) :
    ℝ≥0 :=
  ⟨abv (a : F) ^ characterChangeRectangularExponent j n, pow_nonneg (abv.nonneg _) _⟩

theorem characterChangeRectangularModulus_ne_zero (abv : AbsoluteValue F ℝ)
    (a : Fˣ) (j n : ℕ) :
    characterChangeRectangularModulus abv a j n ≠ 0 := by
  intro h
  exact pow_ne_zero (characterChangeRectangularExponent j n)
    (abv.ne_zero (Units.ne_zero a)) (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)

variable [TopologicalSpace F] [IsTopologicalRing F]
variable (abv : AbsoluteValue F ℝ) (a : Fˣ) (j n : ℕ)
variable [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]

/-- The rectangular Haar scaling obligation, stated for an explicit measure. -/
def HasCharacterChangeRectangularMeasureLaw
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)) : Prop :=
  Measure.map (characterChangeRectangular a j n) ν =
    (characterChangeRectangularModulus abv a j n : ℝ≥0∞) • ν

/-- Conditional rectangular change of variables for total complex integrals. -/
theorem integral_characterChangeRectangular
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν)
    (f : Matrix (Fin j) (Fin (n + 1)) F → ℂ) :
    (∫ x, f (characterChangeRectangular a j n x) ∂ν) =
      ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ) * ∫ x, f x ∂ν := by
  change (∫ x, f ((characterChangeRectangularContinuous a j n).toHomeomorph.toMeasurableEquiv x)
    ∂ν) = _
  rw [← integral_map_equiv
    (characterChangeRectangularContinuous a j n).toHomeomorph.toMeasurableEquiv f]
  change (∫ x, f x ∂Measure.map (characterChangeRectangular a j n) ν) = _
  rw [hν, integral_smul_measure]
  simp [Complex.real_smul]

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F))
variable (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))

/-- The combined change on quotient and rectangular variables. -/
def characterChangeProduct :
    LeftUnipotentQuotient n F × Matrix (Fin j) (Fin (n + 1)) F ≃ᵐ
      LeftUnipotentQuotient n F × Matrix (Fin j) (Fin (n + 1)) F :=
  (characterChangeQuotient a n).toMeasurableEquiv.prodCongr
    (characterChangeRectangularContinuous a j n).toHomeomorph.toMeasurableEquiv

@[simp] theorem characterChangeProduct_apply
    (qx : LeftUnipotentQuotient n F × Matrix (Fin j) (Fin (n + 1)) F) :
    characterChangeProduct a j n qx =
      (characterChangeQuotient a n qx.1, characterChangeRectangular a j n qx.2) := rfl

/-- The two explicit measure laws combine on the product measure. -/
theorem map_characterChangeProduct [SFinite μ] [SFinite ν]
    (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν) :
    Measure.map (characterChangeProduct a j n) (μ.prod ν) =
      ((characterChangeModulus abv a n : ℝ≥0∞) *
        (characterChangeRectangularModulus abv a j n : ℝ≥0∞)) • μ.prod ν := by
  change Measure.map (Prod.map (characterChangeQuotient a n)
    (characterChangeRectangular a j n)) (μ.prod ν) = _
  have hS : Measurable (characterChangeRectangular a j n) :=
    (characterChangeRectangularContinuous a j n).continuous.measurable
  rw [← Measure.map_prod_map μ ν (characterChangeQuotient a n).continuous.measurable
    hS, hμ, hν,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- Product integrability is unchanged under the explicit nonzero finite multipliers. -/
theorem integrable_characterChangeProduct_iff [SFinite μ] [SFinite ν]
    (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν)
    (f : LeftUnipotentQuotient n F × Matrix (Fin j) (Fin (n + 1)) F → ℂ) :
    Integrable (fun qx => f (characterChangeProduct a j n qx)) (μ.prod ν) ↔
      Integrable f (μ.prod ν) := by
  change Integrable (f ∘ characterChangeProduct a j n) (μ.prod ν) ↔ _
  rw [← integrable_map_equiv (characterChangeProduct a j n) f,
    map_characterChangeProduct abv a j n μ ν hμ hν]
  exact integrable_smul_measure
    (mul_ne_zero (by exact_mod_cast characterChangeModulus_ne_zero abv a n)
      (by exact_mod_cast characterChangeRectangularModulus_ne_zero abv a j n))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)

variable (ψ : UnitaryAdditiveCharacter F) (k : ℕ)

/-- The conditional formula for the actual iterated unequal-rank integral.
No product-integrability assumption is needed for this total-integral identity. -/
theorem unequalRankIntegral_characterChange
    (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    determinantWeight abv (characterChangeElement a n)
        (s - ((j + k + 1 : ℕ) : ℂ) / 2) *
      unequalRankIntegral (ψ.scale a) abv j k μ ν
        (unequalRankCharacterChangeFunction ψ a n j k W)
        (characterChangeInverseFunction ψ n a W') s =
    ((characterChangeModulus abv a n : ℝ) : ℂ) *
      ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ) *
        unequalRankIntegral ψ abv j k μ ν W W' s := by
  unfold unequalRankIntegral
  calc
    _ = ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W W' s
        (characterChangeRectangular a j n x) (characterChangeQuotient a n q) ∂ν ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact (unequalRankIntegrand_characterChange ψ a n j k abv W W' s x q).symm
    _ = ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ) *
        ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W W' s x
          (characterChangeQuotient a n q) ∂ν ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      exact integral_characterChangeRectangular abv a j n ν hν
        (fun x => unequalRankIntegrand ψ abv j k W W' s x (characterChangeQuotient a n q))
    _ = _ := by
      rw [integral_characterChangeQuotient abv a μ hμ
        (fun q => ∫ x, unequalRankIntegrand ψ abv j k W W' s x q ∂ν), Complex.real_smul]
      ring

/-- Absolute convergence of the actual product integrand is equivalent for
the original and corrected data. -/
theorem unequalRankConverges_characterChange_iff [SFinite μ] [SFinite ν]
    (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν)
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    UnequalRankConverges (ψ.scale a) abv j k μ ν
      (unequalRankCharacterChangeFunction ψ a n j k W)
      (characterChangeInverseFunction ψ n a W') s ↔
      UnequalRankConverges ψ abv j k μ ν W W' s := by
  have h := integrable_characterChangeProduct_iff abv a j n μ ν hμ hν
    (fun qx => unequalRankIntegrand ψ abv j k W W' s qx.2 qx.1)
  simp only [characterChangeProduct_apply, unequalRankIntegrand_characterChange] at h
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (determinantWeight_ne_zero abv (characterChangeElement a n) _))] at h
  exact h

end Langlands.RankinSelberg
