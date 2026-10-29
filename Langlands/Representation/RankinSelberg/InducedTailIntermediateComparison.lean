import Langlands.Representation.RankinSelberg.InducedTailIntermediateLocalization
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! # Product integration and weights for the intermediate tail comparison -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear MeasureTheory
open scoped ENNReal

universe uF uQ uX uH

section Volumes

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
variable (η : Measure X) [η.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts η]

/-- A nonempty compact open localization set has strictly positive real volume. -/
theorem compactOpen_volume_pos {S : Set X} (hSc : IsCompact S) (hSo : IsOpen S)
    (hSn : S.Nonempty) : 0 < η.real S :=
  ENNReal.toReal_pos (hSo.measure_ne_zero η hSn) hSc.measure_ne_top

variable {H : Type uH} [TopologicalSpace H] [MeasurableSpace H]
variable (ρ : Measure H) [ρ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ρ]

/-- The chart normalization and both compact volumes give a nonzero real scalar. -/
theorem compactOpen_comparisonScalar_pos {S : Set X} {U : Set H}
    (hSc : IsCompact S) (hSo : IsOpen S) (hSn : S.Nonempty)
    (hUc : IsCompact U) (hUo : IsOpen U) (hUn : U.Nonempty)
    {C : ℝ} (hC : 0 < C) : 0 < C * (η.real S * ρ.real U) :=
  mul_pos hC (mul_pos (compactOpen_volume_pos η hSc hSo hSn)
    (compactOpen_volume_pos ρ hUc hUo hUn))

end Volumes

section ProductIntegration

variable {Q : Type uQ} {X : Type uX} {H : Type uH}
variable [MeasurableSpace Q] [MeasurableSpace X] [MeasurableSpace H]
variable {μ : Measure Q} {η : Measure X} {ρ : Measure H}
variable [SFinite μ] [SFinite η] [SFinite ρ]

omit [SFinite μ] in
/-- Absolute integrability survives multiplication by two finite-volume
localization indicators on independent factors. -/
theorem integrable_localized_product {f : Q → ℂ} (hf : Integrable f μ)
    {S : Set X} {U : Set H} (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSfin : η S ≠ ∞) (hUfin : ρ U ≠ ∞) :
    Integrable (fun z : Q × (X × H) =>
      f z.1 * (S.indicator (fun _ => (1 : ℂ)) z.2.1 *
        U.indicator (fun _ => (1 : ℂ)) z.2.2)) (μ.prod (η.prod ρ)) := by
  have hSI : Integrable (S.indicator (fun _ => (1 : ℂ))) η :=
    (integrableOn_const hSfin).integrable_indicator hS
  have hUI : Integrable (U.indicator (fun _ => (1 : ℂ))) ρ :=
    (integrableOn_const hUfin).integrable_indicator hU
  exact hf.mul_prod (hSI.mul_prod hUI)

/-- The actual product integral equals the original integral times both real
volumes. This identity alone makes no convergence assertion. -/
theorem integral_localized_product (f : Q → ℂ)
    {S : Set X} {U : Set H} (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (∫ z : Q × (X × H),
      f z.1 * (S.indicator (fun _ => (1 : ℂ)) z.2.1 *
        U.indicator (fun _ => (1 : ℂ)) z.2.2) ∂μ.prod (η.prod ρ)) =
      ((η.real S * ρ.real U : ℝ) : ℂ) * ∫ q, f q ∂μ := by
  calc
    _ = (∫ q, f q ∂μ) *
        ∫ z : X × H, S.indicator (fun _ => (1 : ℂ)) z.1 *
          U.indicator (fun _ => (1 : ℂ)) z.2 ∂η.prod ρ :=
      integral_prod_mul f (fun z : X × H =>
        S.indicator (fun _ => (1 : ℂ)) z.1 *
          U.indicator (fun _ => (1 : ℂ)) z.2)
    _ = _ := ?_
  rw [integral_prod_mul (S.indicator (fun _ => (1 : ℂ)))
    (U.indicator (fun _ => (1 : ℂ)))]
  simp only [integral_indicator_const (1 : ℂ) hS, integral_indicator_const (1 : ℂ) hU,
    Complex.real_smul, mul_one, Complex.ofReal_mul]
  exact mul_comm _ _

/-- A positive chart normalization remains explicit in the localized integral. -/
theorem integral_localized_product_smul (f : Q → ℂ) (C : ℝ≥0∞)
    {S : Set X} {U : Set H} (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (∫ z : Q × (X × H),
      f z.1 * (S.indicator (fun _ => (1 : ℂ)) z.2.1 *
        U.indicator (fun _ => (1 : ℂ)) z.2.2)
        ∂C • (μ.prod (η.prod ρ))) =
      ((C.toReal * (η.real S * ρ.real U) : ℝ) : ℂ) * ∫ q, f q ∂μ := by
  rw [integral_smul_measure, integral_localized_product f hS hU]
  simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end ProductIntegration

section Weights

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ)

/-- Simultaneous reindexing preserves the actual determinant weight. -/
theorem determinantWeight_reindex {a b : ℕ} (e : Fin a ≃ Fin b)
    (g : Langlands.GeneralLinear a F) (s : ℂ) :
    determinantWeight abv (reindex e g) s = determinantWeight abv g s := by
  unfold determinantWeight
  change (abv (Matrix.det (Matrix.reindex e e g.val)) : ℂ) ^ s = _
  rw [Matrix.det_reindex_self]

/-- The determinant of the actual two-block lower chart is the product of its
diagonal block determinants. -/
theorem det_lowerBlockPair {a d : ℕ} (g : Langlands.GeneralLinear a F)
    (x : Matrix (Fin d) (Fin a) F) (h : lowerTriangularSubgroup d F) :
    Matrix.det (lowerBlockPair g x h).val =
      Matrix.det g.val * Matrix.det h.val.val := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 x h.val.val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

/-- A lower-triangular perturbation of determinant norm one contributes no
spectral weight. -/
theorem determinantWeight_lowerBlockPair {a d : ℕ}
    (g : Langlands.GeneralLinear a F) (x : Matrix (Fin d) (Fin a) F)
    (h : lowerTriangularSubgroup d F) (hh : abv (Matrix.det h.val.val) = 1)
    (s : ℂ) :
    determinantWeight abv (lowerBlockPair g x h) s = determinantWeight abv g s := by
  simp only [determinantWeight, det_lowerBlockPair, map_mul, hh, mul_one]

/-- The extension half-modulus, full integral weight and small-quotient density
combine to the tail weight. Here `d` is the test rank minus the tail rank and
`c` is the full rank minus the test rank. -/
theorem extensionWeight_density_cancel {a : ℕ} (g : Langlands.GeneralLinear a F)
    (d c : ℕ) (s : ℂ) :
    ((Real.rpow (abv (Matrix.det g.val)) (((d + c : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
      determinantWeight abv g (s - (c : ℂ) / 2) *
      (((abv (Matrix.det g.val)) ^ (-(d : ℤ)) : ℝ) : ℂ) =
      determinantWeight abv g (s - (d : ℂ) / 2) := by
  have hg : (abv (Matrix.det g.val) : ℂ) ≠ 0 := by
    exact_mod_cast (abv.ne_zero (determinant g).ne_zero)
  rw [Real.rpow_eq_pow, Complex.ofReal_cpow (abv.nonneg (Matrix.det g.val))
    (((d + c : ℕ) : ℝ) / 2), Complex.ofReal_zpow,
    ← Complex.cpow_intCast]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Int.cast_neg, Int.cast_natCast, Nat.cast_add]
  change _ * (abv (Matrix.det g.val) : ℂ) ^ (s - (c : ℂ) / 2) * _ =
    (abv (Matrix.det g.val) : ℂ) ^ (s - (d : ℂ) / 2)
  rw [← Complex.cpow_add _ _ hg, ← Complex.cpow_add _ _ hg]
  congr 1
  ring

end Weights

end Langlands.RankinSelberg.InducedTailIntermediate
