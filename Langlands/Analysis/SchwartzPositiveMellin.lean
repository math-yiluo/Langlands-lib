import Langlands.Analysis.SchwartzMellinIntegrationByParts
import Langlands.Analysis.SchwartzProductMajorant
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy

/-! # Initial convergence for Mellin integrals on the positive orthant -/

noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {ι : Type*} [Fintype ι]

/-- Lebesgue measure restricted to the positive half-line. -/
abbrev positiveLineMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- The product of positive real half-line measures. -/
def positiveCoordinateMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => positiveLineMeasure)

instance positiveCoordinateMeasure_sigmaFinite : SigmaFinite (positiveCoordinateMeasure ι) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun _ : ι => positiveLineMeasure)))

theorem ae_positiveCoordinates :
    ∀ᵐ x ∂positiveCoordinateMeasure ι, ∀ i, 0 < x i := by
  apply eventually_all.2
  intro i
  have h := Measure.tendsto_eval_ae_ae (μ := fun _ : ι => positiveLineMeasure) (i := i)
  exact h.eventually (ae_restrict_mem measurableSet_Ioi)

private theorem continuous_polynomialDamping (p : ℕ) :
    Continuous (fun x : ℝ => ((((1 + ‖x‖) ^ p)⁻¹ : ℝ) : ℂ)) := by
  have h : Continuous (fun x : ℝ => (1 + ‖x‖) ^ p) :=
    (continuous_const.add continuous_norm).pow p
  exact Complex.continuous_ofReal.comp (h.inv₀ (fun x => pow_ne_zero _
    (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg x)))))

/-- A positive-line Mellin weight becomes integrable with sufficient polynomial damping. -/
theorem integrable_positiveLine_damped_cpow {s : ℂ} (hs : 0 < s.re) (p : ℕ) (hp : s.re < p) :
    Integrable (fun x : ℝ => ‖(x : ℂ) ^ (s - 1)‖ * ((1 + ‖x‖) ^ p)⁻¹)
      positiveLineMeasure := by
  let f (x : ℝ) : ℂ := ((((1 + ‖x‖) ^ p)⁻¹ : ℝ) : ℂ)
  have hc : Continuous f := continuous_polynomialDamping p
  have hf (x : ℝ) : ‖f x‖ = ((1 + ‖x‖) ^ p)⁻¹ := Complex.norm_of_nonneg (by positivity)
  have hTop : f =O[atTop] (fun x : ℝ => x ^ (-(p : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hf, Real.rpow_neg hx.le, Real.rpow_natCast,
      Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hx.le p)), one_mul]
    have h : x ≤ 1 + ‖x‖ := (le_abs_self x).trans (le_add_of_nonneg_left zero_le_one)
    exact (inv_le_inv₀ (pow_pos (by positivity) p) (pow_pos hx p)).2
      (pow_le_pow_left₀ hx.le h p)
  have hBot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [hf, neg_zero, Real.rpow_zero, norm_one, one_mul]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x)))
  have hI : MellinConvergent f s :=
    mellinConvergent_of_isBigO_rpow
      (hc.locallyIntegrable.locallyIntegrableOn (Ioi 0)) hTop hp hBot hs
  exact hI.norm.congr (Eventually.of_forall fun x => by
    change ‖(x : ℂ) ^ (s - 1) • f x‖ = _
    rw [norm_smul, hf])

/-- The product Mellin kernel on real positive coordinates. -/
def coordinateMellinIntegrand (Φ : (ι → ℝ) → ℂ) (s : ι → ℂ) (x : ι → ℝ) : ℂ :=
  Φ x * ∏ i, (x i : ℂ) ^ (s i - 1)

/-- The Mellin integral before meromorphic continuation. -/
def coordinateMellin (Φ : (ι → ℝ) → ℂ) (s : ι → ℂ) : ℂ :=
  ∫ x, coordinateMellinIntegrand Φ s x ∂positiveCoordinateMeasure ι

theorem measurable_ofReal_cpow_const (s : ℂ) :
    Measurable (fun x : ℝ => (x : ℂ) ^ s) := by
  simp_rw [Complex.cpow_def]
  refine Measurable.ite (measurableSet_eq_fun Complex.continuous_ofReal.measurable measurable_const)
    measurable_const ?_
  exact Complex.continuous_exp.measurable.comp
    ((Complex.measurable_log.comp Complex.continuous_ofReal.measurable).mul_const s)

theorem integrable_coordinateMellinIntegrand (Φ : SchwartzMap (ι → ℝ) ℂ)
    {s : ι → ℂ} (hs : ∀ i, 0 < (s i).re) :
    Integrable (coordinateMellinIntegrand Φ s) (positiveCoordinateMeasure ι) := by
  obtain ⟨b, hb⟩ := Finite.exists_le (fun i => (s i).re)
  obtain ⟨p, hp⟩ := exists_nat_gt b
  exact integrable_schwartz_mul_coordinateWeights Φ (fun _ => positiveLineMeasure)
    (fun i x => (x : ℂ) ^ (s i - 1))
    (fun i => measurable_ofReal_cpow_const (s i - 1)) p
    (fun i => integrable_positiveLine_damped_cpow (hs i) p ((hb i).trans_lt hp))

private theorem ofReal_cpow_eq_exp_log {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, mul_comm]

/-- The product Mellin integral is holomorphic on its domain of convergence
along every complex affine line with real coordinate slopes. -/
theorem differentiableOn_coordinateMellin_affine (Φ : SchwartzMap (ι → ℝ) ℂ)
    (c : ι → ℝ) (b : ι → ℂ) :
    DifferentiableOn ℂ
      (fun z : ℂ => coordinateMellin Φ (fun i => (c i : ℂ) * z + b i))
      {z | ∀ i, 0 < ((c i : ℂ) * z + b i).re} := by
  let A (x : ι → ℝ) := Φ x * ∏ i, (x i : ℂ) ^ (b i - 1)
  let B (x : ι → ℝ) := ∑ i, c i * Real.log (x i)
  let S : Set ℂ := {z | ∀ i, 0 < ((c i : ℂ) * z + b i).re}
  have hB : Measurable B :=
    Finset.measurable_sum _ fun i _ =>
      (Real.measurable_log.comp (measurable_pi_apply i)).const_mul _
  have hS : IsOpen S := by
    rw [show S = ⋂ i, {z : ℂ | 0 < ((c i : ℂ) * z + b i).re} from by
      ext z
      simp [S]]
    exact isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by fun_prop)
  have hEq (z : ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
      coordinateMellinIntegrand Φ (fun i => (c i : ℂ) * z + b i) x =
        A x * Complex.exp (z * (B x : ℂ)) := by
    have h (i : ι) :
        ((x i : ℂ) ^ ((c i : ℂ) * z + b i - 1)) =
          (x i : ℂ) ^ (b i - 1) * Complex.exp (z * ((c i * Real.log (x i) : ℝ) : ℂ)) := by
      rw [show (c i : ℂ) * z + b i - 1 = (b i - 1) + z * (c i : ℂ) by ring,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hx i).ne'),
        ofReal_cpow_eq_exp_log (hx i) (z * (c i : ℂ)), Complex.ofReal_mul, mul_assoc]
    simp only [coordinateMellinIntegrand, A, B, h, Finset.prod_mul_distrib,
      ← Complex.exp_sum, Complex.ofReal_sum, Finset.mul_sum, mul_assoc]
  have hInt (z : ℂ) (hz : z ∈ S) :
      Integrable (fun x => A x * Complex.exp (z * (B x : ℂ))) (positiveCoordinateMeasure ι) :=
    (integrable_coordinateMellinIntegrand Φ hz).congr (ae_positiveCoordinates.mono (hEq z))
  have hdiff := Langlands.Global.RankinSelbergGlobal.differentiableOn_integral_mul_cexp hB hS hInt
  refine hdiff.congr fun z _ => ?_
  exact integral_congr_ae (ae_positiveCoordinates.mono (hEq z))

end Langlands.Analysis
