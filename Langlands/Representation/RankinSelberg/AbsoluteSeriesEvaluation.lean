import Langlands.Representation.RankinSelberg.ComplexCauchySeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Absolute evaluation of finite products of complex power series -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- Absolute summability of the coefficients of a complex formal series at a parameter. -/
def AbsolutelyEvaluable (H : PowerSeries ℂ) (t : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖PowerSeries.coeff n H * t ^ n‖)

/-- The complex series value, used with an explicit absolute summability proof. -/
def seriesValue (H : PowerSeries ℂ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n H * t ^ n

/-- Coefficient evaluation commutes with the finite convolution in a product. -/
theorem coeff_mul_scaled (F G : PowerSeries ℂ) (t : ℂ) (n : ℕ) :
    PowerSeries.coeff n (F * G) * t ^ n =
      ∑ ab ∈ Finset.antidiagonal n,
        (PowerSeries.coeff ab.1 F * t ^ ab.1) *
          (PowerSeries.coeff ab.2 G * t ^ ab.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← Finset.mem_antidiagonal.mp hab, pow_add]
  ring

theorem absolutelyEvaluable_one (t : ℂ) : AbsolutelyEvaluable 1 t := by
  have h : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 (1 : ℝ)).summable
  apply h.congr
  intro n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

theorem seriesValue_one (t : ℂ) : seriesValue 1 t = 1 := by
  simp [seriesValue, PowerSeries.coeff_one]

/-- Absolute summability is preserved by power series multiplication. -/
theorem AbsolutelyEvaluable.mul {F G : PowerSeries ℂ} {t : ℂ}
    (hF : AbsolutelyEvaluable F t) (hG : AbsolutelyEvaluable G t) :
    AbsolutelyEvaluable (F * G) t := by
  unfold AbsolutelyEvaluable at hF hG ⊢
  simpa only [coeff_mul_scaled] using
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG)

/-- The Cauchy-product theorem evaluates a product of absolutely evaluable series. -/
theorem seriesValue_mul {F G : PowerSeries ℂ} {t : ℂ}
    (hF : AbsolutelyEvaluable F t) (hG : AbsolutelyEvaluable G t) :
    seriesValue (F * G) t = seriesValue F t * seriesValue G t := by
  unfold seriesValue
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG]
  simp_rw [coeff_mul_scaled]

/-- Absolute summability of a finite product follows from its factors. -/
theorem absolutelyEvaluable_finset_prod {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries ℂ) (t : ℂ) (h : ∀ i ∈ s, AbsolutelyEvaluable (F i) t) :
    AbsolutelyEvaluable (∏ i ∈ s, F i) t := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using absolutelyEvaluable_one t
  | @insert a s ha ih =>
    intro h
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Evaluation commutes with a finite product of absolutely evaluable series. -/
theorem seriesValue_finset_prod {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries ℂ) (t : ℂ) (h : ∀ i ∈ s, AbsolutelyEvaluable (F i) t) :
    seriesValue (∏ i ∈ s, F i) t = ∏ i ∈ s, seriesValue (F i) t := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using seriesValue_one t
  | @insert a s ha ih =>
    intro h
    have hs := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha,
      seriesValue_mul (h a (Finset.mem_insert_self _ _))
        (absolutelyEvaluable_finset_prod s F t hs), ih hs, Finset.prod_insert ha]

/-- A geometric series is absolutely evaluable inside its disk. -/
theorem absolutelyEvaluable_geometric (a t : ℂ) (h : ‖a * t‖ < 1) :
    AbsolutelyEvaluable (PowerSeries.mk (fun n : ℕ => a ^ n)) t := by
  unfold AbsolutelyEvaluable
  simpa only [PowerSeries.coeff_mk, ← mul_pow] using
    (summable_norm_geometric_of_norm_lt_one h)

theorem seriesValue_geometric (a t : ℂ) (h : ‖a * t‖ < 1) :
    seriesValue (PowerSeries.mk (fun n : ℕ => a ^ n)) t = (1 - a * t)⁻¹ := by
  unfold seriesValue
  simpa only [PowerSeries.coeff_mk, ← mul_pow] using (tsum_geometric_of_norm_lt_one h)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Absolute convergence of the complete Cauchy series in the pair-product disk. -/
theorem absolutelyEvaluable_complexCauchySeries {n : ℕ}
    (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (t : ℂ)
    (h : ∀ i j, ‖x i * y j * t‖ < 1) :
    AbsolutelyEvaluable (complexCauchySeries x y) t := by
  rw [complexCauchySeries_eq_geometric]
  apply absolutelyEvaluable_finset_prod
  intro j _
  apply absolutelyEvaluable_finset_prod
  intro i _
  exact absolutelyEvaluable_geometric _ _ (h i j)

/-- Analytic evaluation of the Cauchy coefficient series as the Euler product. -/
theorem seriesValue_complexCauchySeries {n : ℕ}
    (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (t : ℂ)
    (h : ∀ i j, ‖x i * y j * t‖ < 1) :
    seriesValue (complexCauchySeries x y) t =
      (∏ j : Fin (n + 1), ∏ i : σ, (1 - x i * y j * t))⁻¹ := by
  rw [complexCauchySeries_eq_geometric]
  rw [seriesValue_finset_prod _ _ t (fun j _ =>
    absolutelyEvaluable_finset_prod _ _ t (fun i _ =>
      absolutelyEvaluable_geometric _ _ (h i j)))]
  simp_rw [seriesValue_finset_prod _ _ t (fun i _ =>
    absolutelyEvaluable_geometric _ _ (h i _))]
  simp_rw [seriesValue_geometric _ _ (h _ _)]
  simp [Finset.prod_inv_distrib]

end Langlands.GeneralLinear.Spherical
