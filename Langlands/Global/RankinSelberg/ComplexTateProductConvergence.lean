import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi

/-! # Convergence of finite products of complex Tate weights -/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

/-- The angular Tate weight relative to additive complex Lebesgue measure. -/
def additiveWeight (m : ℤ) (u z : ℂ) : ℂ :=
  if z = 0 then 0 else (z / (‖z‖ : ℂ)) ^ m * (‖z‖ : ℂ) ^ (2 * u - 2)

theorem measurable_additiveWeight (m : ℤ) (u : ℂ) : Measurable (additiveWeight m u) := by
  unfold additiveWeight
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

theorem norm_additiveWeight {z : ℂ} (hz : z ≠ 0) (m : ℤ) (u : ℂ) :
    ‖additiveWeight m u z‖ = ‖z‖ ^ (2 * u.re - 2) := by
  simp [additiveWeight, hz, norm_zpow,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hz), Complex.mul_re, Complex.sub_re]

private def coordinateMajorant (q : ℕ) (a r : ℝ) : ℝ :=
  r ^ (2 * a - 2) * (max 1 r ^ q)⁻¹

private theorem integrable_coordinateMajorant (q : ℕ) {a : ℝ} (ha : 0 < a)
    (hq : 2 * a < q) : Integrable (fun z : ℂ => coordinateMajorant q a ‖z‖) volume := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  rw [← Ioo_union_Ici_eq_Ioi (zero_lt_one : (0 : ℝ) < 1), integrableOn_union]
  constructor
  · refine ((intervalIntegral.integrableOn_Ioo_rpow_iff (zero_lt_one : (0 : ℝ) < 1)).2
      (show -1 < 2 * a - 1 by linarith)).congr_fun ?_ measurableSet_Ioo
    intro r hr
    change r ^ (2 * a - 1) = r * coordinateMajorant q a r
    rw [coordinateMajorant, max_eq_left hr.2.le, one_pow, inv_one, mul_one]
    have hp := Real.rpow_add hr.1 1 (2 * a - 2)
    rw [Real.rpow_one] at hp
    convert hp using 1
    congr 1
    ring
  · refine ((integrableOn_Ioi_rpow_of_lt (a := 2 * a - 1 - q) (by linarith) zero_lt_one).congr_set_ae
      Ioi_ae_eq_Ici.symm).congr_fun ?_ measurableSet_Ici
    intro r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    change r ^ (2 * a - 1 - q) = r * coordinateMajorant q a r
    rw [coordinateMajorant, max_eq_right hr, ← Real.rpow_natCast, ← Real.rpow_neg hr0.le,
      ← Real.rpow_add hr0]
    have hp := Real.rpow_add hr0 1 (2 * a - 2 - q)
    rw [Real.rpow_one] at hp
    convert hp using 1
    congr 1
    ring

variable {ι : Type*} [Fintype ι]

/-- Product integrand with independent angular and spectral parameters in each coordinate. -/
def integrand (F : (ι → ℂ) → ℂ) (m : ι → ℤ) (u : ι → ℂ) (z : ι → ℂ) : ℂ :=
  F z * ∏ j, additiveWeight (m j) (u j) (z j)

theorem measurable_integrand {F : (ι → ℂ) → ℂ} (hF : Measurable F)
    (m : ι → ℤ) (u : ι → ℂ) : Measurable (integrand F m u) := by
  exact hF.mul (Finset.measurable_prod _ fun j _ =>
    (measurable_additiveWeight (m j) (u j)).comp (measurable_pi_apply j))

theorem exists_norm_le_prod_decay (F : 𝓢(ι → ℂ, ℂ)) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖F z‖ ≤ C * ∏ j, (max 1 ‖z j‖ ^ q)⁻¹ := by
  let k := q * Fintype.card ι
  let C := max (SchwartzMap.seminorm ℝ 0 0 F) (SchwartzMap.seminorm ℝ k 0 F)
  refine ⟨C, (apply_nonneg _ _).trans (le_max_left (SchwartzMap.seminorm ℝ 0 0 F) _), fun z => ?_⟩
  have hsem : (max 1 ‖z‖) ^ k * ‖F z‖ ≤ C := by
    rcases le_or_gt ‖z‖ 1 with h | h
    · rw [max_eq_left h, one_pow, one_mul]
      exact (SchwartzMap.norm_le_seminorm ℝ F z).trans (le_max_left _ _)
    · rw [max_eq_right h.le]
      exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ F k z).trans (le_max_right _ _)
  let D := ∏ j, max 1 ‖z j‖ ^ q
  have hD : 0 < D := Finset.prod_pos fun j _ => pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _
  have hle : D ≤ (max 1 ‖z‖) ^ k := by
    calc
      D ≤ ∏ _j : ι, max 1 ‖z‖ ^ q := by
        refine Finset.prod_le_prod₀
          (fun j _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (fun j _ => ?_)
        exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
          (max_le_max_left _ (norm_le_pi_norm z j)) _
      _ = (max 1 ‖z‖) ^ k := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hD, mul_comm]
  exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hsem

theorem integrable_integrand (F : 𝓢(ι → ℂ, ℂ)) (m : ι → ℤ) {u : ι → ℂ}
    (hu : ∀ j, 0 < (u j).re) : Integrable (integrand F m u) volume := by
  obtain ⟨q, hq⟩ := exists_nat_gt (∑ j, 2 * (u j).re)
  have hq' (j : ι) : 2 * (u j).re < q :=
    (Finset.single_le_sum (f := fun i => 2 * (u i).re)
      (fun i _ => mul_nonneg (by norm_num) (hu i).le) (Finset.mem_univ j)).trans_lt hq
  obtain ⟨C, _, hF⟩ := exists_norm_le_prod_decay F q
  have hmaj : Integrable (fun z : ι → ℂ => ∏ j, coordinateMajorant q (u j).re ‖z j‖) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun j => integrable_coordinateMajorant q (hu j) (hq' j)
  refine (hmaj.const_mul C).mono' (measurable_integrand F.continuous.measurable m u).aestronglyMeasurable ?_
  have hne : ∀ᵐ z : ι → ℂ ∂volume, ∀ j, z j ≠ 0 := by
    rw [volume_pi, ae_all_iff]
    exact fun j => Measure.ae_eval_ne (fun _ : ι => (volume : Measure ℂ)) j 0
  filter_upwards [hne] with z hz
  rw [integrand, norm_mul, norm_prod]
  simp only [norm_additiveWeight (hz _), coordinateMajorant, Finset.prod_mul_distrib]
  calc
    _ ≤ (C * ∏ j, (max 1 ‖z j‖ ^ q)⁻¹) * ∏ j, ‖z j‖ ^ (2 * (u j).re - 2) :=
      mul_le_mul_of_nonneg_right (hF z) (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

/-- The product Tate integral of a Schwartz function converges absolutely if each real part is positive. -/
def ComplexTateProductConvergenceStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin n → ℂ, ℂ)) (m : Fin n → ℤ) (u : Fin n → ℂ),
    (∀ j, 0 < (u j).re) → Integrable (integrand F m u) volume

theorem complexTateProductConvergence : ComplexTateProductConvergenceStatement :=
  fun _ F m _ hu => integrable_integrand F m hu

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
