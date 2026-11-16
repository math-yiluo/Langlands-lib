import Langlands.Representation.Archimedean.ParabolicChartBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Iterated integrals of products of powers of partial square sums
-/

noncomputable section

open MeasureTheory Set

namespace Langlands.Archimedean

set_option autoImplicit false

namespace PartialSqIntegral

open ParabolicChartBound

/-! ## The line integral `β(d) = ∫_ℝ (1 + t²)^d dt` -/

/-- `β(d) = ∫_ℝ (1 + t²)^d dt`. -/
def lineIntegral (d : ℂ) : ℂ := ∫ t : ℝ, ((1 + t ^ 2 : ℝ) : ℂ) ^ d

theorem continuous_ofReal_cpow {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (hpos : ∀ t, 0 < f t) (d : ℂ) :
    Continuous fun t => ((f t : ℝ) : ℂ) ^ d :=
  (Complex.continuous_ofReal.comp hf).cpow continuous_const
    fun t => Complex.ofReal_mem_slitPlane.mpr (hpos t)

theorem integrable_add_sq_cpow {a : ℝ} (ha : 0 < a) {d : ℂ} (hd : d.re < -1 / 2) :
    Integrable fun t : ℝ => ((a + t ^ 2 : ℝ) : ℂ) ^ d := by
  have hpos : ∀ t : ℝ, 0 < a + t ^ 2 := fun t => by positivity
  have hcont : Continuous fun t : ℝ => ((a + t ^ 2 : ℝ) : ℂ) ^ d :=
    continuous_ofReal_cpow (continuous_const.add (continuous_id.pow 2)) hpos d
  -- `(a + t²)^{Re d} ≤ a^{Re d} (1 + t²/a)^{Re d}`; substitute `t = √a s`.
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hint : Integrable fun t : ℝ => (1 + (t / Real.sqrt a) ^ 2) ^ d.re := by
    have h := (integrable_one_add_sq_rpow hd).comp_div hsq.ne'
    exact h
  refine (hint.const_mul (a ^ d.re)).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun t => le_of_eq ?_)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos t), ← Real.mul_rpow ha.le (by positivity)]
  congr 1
  rw [div_pow, Real.sq_sqrt ha.le]
  field_simp

theorem integrable_one_add_sq_cpow {d : ℂ} (hd : d.re < -1 / 2) :
    Integrable fun t : ℝ => ((1 + t ^ 2 : ℝ) : ℂ) ^ d :=
  integrable_add_sq_cpow one_pos hd

/-- `(1/r)^a = r^{-a}` for `r > 0`. -/
theorem one_div_cpow {r : ℝ} (hr : 0 < r) (a : ℂ) : (1 / (r : ℂ)) ^ a = (r : ℂ) ^ (-a) := by
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact
    Real.pi_pos.ne), Complex.cpow_neg]

/-- **Euler's formula behind `β`.** `(1 + t²)^d Γ(-d) = ∫_0^∞ u^{-d-1} e^{-u} e^{-u t²} du`. -/
theorem one_add_sq_cpow_mul_Gamma {d : ℂ} (hd : d.re < 0) (t : ℝ) :
    ((1 + t ^ 2 : ℝ) : ℂ) ^ d * Complex.Gamma (-d) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-d - 1) * Complex.exp (-(u : ℂ)) *
        ((Real.exp (-u * t ^ 2) : ℝ) : ℂ) := by
  have hr : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := -d) (by simp; linarith) hr
  rw [one_div_cpow hr, neg_neg] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem measurable_integrand (d : ℂ) :
    Measurable fun p : ℝ × ℝ => (p.2 : ℂ) ^ (-d - 1) * Complex.exp (-(p.2 : ℂ)) *
      ((Real.exp (-p.2 * p.1 ^ 2) : ℝ) : ℂ) := by
  have h1 : Measurable fun p : ℝ × ℝ => (p.2 : ℂ) := Complex.measurable_ofReal.comp measurable_snd
  refine ((h1.pow_const _).mul (Complex.measurable_exp.comp h1.neg)).mul ?_
  exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_snd.neg).mul (measurable_fst.pow_const 2)))

theorem norm_integrand {d : ℂ} {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖(u : ℂ) ^ (-d - 1) * Complex.exp (-(u : ℂ)) * ((Real.exp (-u * t ^ 2) : ℝ) : ℂ)‖ =
      u ^ (-d.re - 1) * Real.exp (-u) * Real.exp (-u * t ^ 2) := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

theorem integral_norm_integrand {d : ℂ} {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, ‖(u : ℂ) ^ (-d - 1) * Complex.exp (-(u : ℂ)) * ((Real.exp (-u * t ^ 2) : ℝ) : ℂ)‖ =
      Real.sqrt Real.pi * (Real.exp (-u) * u ^ ((-d.re - 1 / 2) - 1)) := by
  simp_rw [norm_integrand hu]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div' _ hu.le]
  have hs : Real.sqrt u = u ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u
  rw [hs]
  have : u ^ (-d.re - 1 / 2 - 1) = u ^ (-d.re - 1) / u ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_sub hu]
    ring_nf
  rw [this]
  field_simp

theorem integrable_integrand {d : ℂ} (hd : d.re < -1 / 2) :
    Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (-d - 1) * Complex.exp (-(p.2 : ℂ)) *
      ((Real.exp (-p.2 * p.1 ^ 2) : ℝ) : ℂ)) (volume.prod (volume.restrict (Ioi 0))) := by
  rw [integrable_prod_iff' (measurable_integrand d).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
    have hg := (integrable_exp_neg_mul_sq (b := u) hu).ofReal (𝕜 := ℂ)
    show Integrable (fun x : ℝ => (u : ℂ) ^ (-d - 1) * Complex.exp (-(u : ℂ)) *
      ((Real.exp (-u * x ^ 2) : ℝ) : ℂ))
    exact hg.const_mul _
  · have hΓ := Real.GammaIntegral_convergent (s := -d.re - 1 / 2) (by linarith)
    have h2 : IntegrableOn (fun u => Real.sqrt Real.pi * (Real.exp (-u) * u ^ (-d.re - 1 / 2 - 1)))
        (Ioi 0) := hΓ.const_mul _
    exact h2.congr_fun (fun u hu => (integral_norm_integrand hu).symm) measurableSet_Ioi

theorem integral_gaussian_mul {d : ℂ} {u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, (u : ℂ) ^ (-d - 1) * Complex.exp (-(u : ℂ)) * ((Real.exp (-u * t ^ 2) : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * (Complex.exp (-(u : ℂ)) * (u : ℂ) ^ ((-d - 1 / 2) - 1)) := by
  rw [integral_const_mul, integral_complex_ofReal, integral_gaussian, Real.sqrt_div' _ hu.le]
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hs : ((Real.sqrt u : ℝ) : ℂ) = (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
    push_cast
    rfl
  have : (u : ℂ) ^ (-d - 1 / 2 - 1) = (u : ℂ) ^ (-d - 1) / (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_sub _ _ hu']
    ring_nf
  rw [this, Complex.ofReal_div, hs]
  field_simp

/-- **`β(d) ≠ 0`.** Euler's formula and Fubini give `β(d) Γ(-d) = √π Γ(-d - 1/2)`. -/
theorem lineIntegral_mul_Gamma {d : ℂ} (hd : d.re < -1 / 2) :
    lineIntegral d * Complex.Gamma (-d) =
      (Real.sqrt Real.pi : ℂ) * Complex.Gamma (-d - 1 / 2) := by
  have hd0 : d.re < 0 := by linarith
  rw [lineIntegral, ← integral_mul_const]
  simp_rw [one_add_sq_cpow_mul_Gamma hd0]
  rw [integral_integral_swap (integrable_integrand hd)]
  rw [setIntegral_congr_fun measurableSet_Ioi fun u hu => integral_gaussian_mul (d := d) hu]
  rw [integral_const_mul, Complex.Gamma_eq_integral (by simp; linarith), Complex.GammaIntegral]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [Complex.ofReal_exp, Complex.ofReal_neg]

theorem lineIntegral_ne_zero {d : ℂ} (hd : d.re < -1 / 2) : lineIntegral d ≠ 0 := by
  intro h0
  have h := lineIntegral_mul_Gamma hd
  rw [h0, zero_mul] at h
  have hΓ : Complex.Gamma (-d - 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  exact mul_ne_zero hπ hΓ h.symm

/-! ## Rescaling: `∫ (a + t²)^d dt = a^{d + 1/2} β(d)` -/

theorem ofReal_sqrt_eq_cpow {a : ℝ} (ha : 0 ≤ a) :
    ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
  push_cast
  rfl

theorem integral_add_sq_cpow {a : ℝ} (ha : 0 < a) (d : ℂ) :
    ∫ t : ℝ, ((a + t ^ 2 : ℝ) : ℂ) ^ d = (a : ℂ) ^ (d + 1 / 2) * lineIntegral d := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.integral_comp_mul_left (fun t : ℝ => ((a + t ^ 2 : ℝ) : ℂ) ^ d)
    (Real.sqrt a)
  have hpt : ∀ s : ℝ, ((a + (Real.sqrt a * s) ^ 2 : ℝ) : ℂ) ^ d =
      (a : ℂ) ^ d * ((1 + s ^ 2 : ℝ) : ℂ) ^ d := by
    intro s
    rw [mul_pow, Real.sq_sqrt ha.le, show a + a * s ^ 2 = a * (1 + s ^ 2) by ring,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (by positivity)]
  simp only [hpt, integral_const_mul] at h
  rw [abs_of_pos (inv_pos.mpr hs), Complex.real_smul] at h
  have hI : (∫ t : ℝ, ((a + t ^ 2 : ℝ) : ℂ) ^ d) =
      ((Real.sqrt a : ℝ) : ℂ) * ((a : ℂ) ^ d * lineIntegral d) := by
    rw [lineIntegral, h, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr hs.ne'), one_mul]
  rw [hI, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), ofReal_sqrt_eq_cpow ha.le]
  ring

theorem integral_add_sq_rpow {a : ℝ} (ha : 0 < a) (σ : ℝ) :
    ∫ t : ℝ, (a + t ^ 2) ^ σ = a ^ (σ + 1 / 2) * ∫ s : ℝ, (1 + s ^ 2) ^ σ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.integral_comp_mul_left (fun t : ℝ => (a + t ^ 2) ^ σ) (Real.sqrt a)
  have hpt : ∀ s : ℝ, (a + (Real.sqrt a * s) ^ 2) ^ σ = a ^ σ * (1 + s ^ 2) ^ σ := by
    intro s
    rw [mul_pow, Real.sq_sqrt ha.le, show a + a * s ^ 2 = a * (1 + s ^ 2) by ring,
      Real.mul_rpow ha.le (by positivity)]
  simp only [hpt, integral_const_mul, smul_eq_mul] at h
  rw [abs_of_pos (inv_pos.mpr hs)] at h
  have hI : (∫ t : ℝ, (a + t ^ 2) ^ σ) =
      Real.sqrt a * (a ^ σ * ∫ s : ℝ, (1 + s ^ 2) ^ σ) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [hI, Real.rpow_add ha, Real.sqrt_eq_rpow]
  ring

/-! ## Partial square sums of `Fin.snoc` -/

theorem partialSq_snoc_castSucc {m : ℕ} (y : Fin m → ℝ) (t : ℝ) (l : Fin m) :
    partialSq (Fin.snoc y t : Fin (m + 1) → ℝ) ((l : ℕ) + 1) = partialSq y ((l : ℕ) + 1) := by
  unfold partialSq
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have : ¬ (m < (l : ℕ) + 1) := by omega
  simp [this]

theorem partialSq_snoc_last {m : ℕ} (y : Fin m → ℝ) (t : ℝ) :
    partialSq (Fin.snoc y t : Fin (m + 1) → ℝ) (m + 1) = partialSq y m + t ^ 2 := by
  unfold partialSq
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin m, (j : ℕ) < m + 1 := fun j => by omega
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, lt_add_one,
    ite_true, h1, Fin.is_lt]
  ring

theorem continuous_partialSq {m : ℕ} (l : ℕ) : Continuous fun x : Fin m → ℝ => partialSq x l := by
  unfold partialSq
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  split_ifs
  · exact (continuous_apply j).pow 2
  · exact continuous_const

/-! ## Iterated integrals -/

/-- `G(d, c)(x) = r_m(x)^c ∏_{l < m} r_{l+1}(x)^{d_l}` with `r_l = partialSq x l`. -/
def partialSqProd {m : ℕ} (d : Fin m → ℂ) (c : ℂ) (x : Fin m → ℝ) : ℂ :=
  ((partialSq x m : ℝ) : ℂ) ^ c * ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ d l

/-- The tail condition `Re c + ∑_{l ≥ j} (Re d_l + 1/2) < 0` for every `j`. -/
def TailCondition {m : ℕ} (d : Fin m → ℂ) (c : ℂ) : Prop :=
  ∀ j : Fin m, c.re + ∑ l : Fin m, (if j ≤ l then (d l).re + 1 / 2 else 0) < 0

theorem continuous_partialSqProd {m : ℕ} (d : Fin m → ℂ) (c : ℂ) :
    Continuous (partialSqProd d c) := by
  unfold partialSqProd
  refine Continuous.mul ?_ (continuous_finsetProd _ fun l _ => ?_)
  · exact continuous_ofReal_cpow (f := fun x : Fin m → ℝ => partialSq x m)
      (continuous_partialSq m) (fun x => partialSq_pos x m) c
  · exact continuous_ofReal_cpow (f := fun x : Fin m → ℝ => partialSq x ((l : ℕ) + 1))
      (continuous_partialSq _) (fun x => partialSq_pos x _) _

theorem norm_partialSqProd {m : ℕ} (d : Fin m → ℂ) (c : ℂ) (x : Fin m → ℝ) :
    ‖partialSqProd d c x‖ =
      partialSq x m ^ c.re * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ (d l).re := by
  unfold partialSqProd
  rw [norm_mul, norm_prod, Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos x m)]
  congr 1
  exact Finset.prod_congr rfl fun l _ =>
    Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos x _) _

/-- **Iterated integrals of products of partial square sums.** Under the tail condition,
`G(d, c)` is integrable on `ℝ^m` and its integral does not vanish. -/
theorem integrable_and_integral_ne_zero : ∀ (m : ℕ) (d : Fin m → ℂ) (c : ℂ), TailCondition d c →
    Integrable (partialSqProd d c) ∧ ∫ x, partialSqProd d c x ≠ 0
  | 0, d, c, _ => by
      have hG : partialSqProd d c = fun _ => (1 : ℂ) := by
        funext x
        simp [partialSqProd, partialSq_zero]
      rw [hG]
      refine ⟨integrable_const _, ?_⟩
      rw [integral_const, measureReal_def, volume_pi, Measure.pi_univ]
      simp
  | m + 1, d, c, hd => by
      set β : ℂ := c + d (Fin.last m) with hβdef
      have hβ : β.re < -1 / 2 := by
        have := hd (Fin.last m)
        have hsum : (∑ l : Fin (m + 1), (if Fin.last m ≤ l then (d l).re + 1 / 2 else 0)) =
            (d (Fin.last m)).re + 1 / 2 := by
          rw [Fin.sum_univ_castSucc]
          simp
        rw [hsum] at this
        simp only [hβdef, Complex.add_re]
        linarith
      set d' : Fin m → ℂ := fun l => d (Fin.castSucc l) with hd'def
      obtain ⟨hIHi, hIHn⟩ := integrable_and_integral_ne_zero m d' (β + 1 / 2) (fun j => by
        have := hd (Fin.castSucc j)
        rw [Fin.sum_univ_castSucc] at this
        simp only [Fin.castSucc_le_castSucc_iff, Fin.le_last, ite_true] at this
        simp only [hd'def, hβdef, Complex.add_re, Complex.div_re, Complex.one_re,
          Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        norm_num at this ⊢
        linarith)
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
      set H : ℝ × (Fin m → ℝ) → ℂ := fun p =>
        ((partialSq p.2 m + p.1 ^ 2 : ℝ) : ℂ) ^ β *
          ∏ l : Fin m, ((partialSq p.2 ((l : ℕ) + 1) : ℝ) : ℂ) ^ d' l with hHdef
      have key : partialSqProd d c ∘ e.symm = H := by
        funext p
        obtain ⟨t, y⟩ := p
        simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hHdef,
          partialSqProd]
        have hx : (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) (Fin.last m)) (t, y) =
            (Fin.snoc y t : Fin (m + 1) → ℝ) := Fin.insertNth_last' _ _
        rw [hx, Fin.prod_univ_castSucc]
        simp only [partialSq_snoc_castSucc, Fin.val_castSucc, Fin.val_last]
        rw [partialSq_snoc_last]
        have hpos : 0 < partialSq y m + t ^ 2 := by
          have := partialSq_pos y m
          positivity
        rw [hβdef, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]
        simp only [hd'def]
        ring
      have hHc : Continuous H := by
        refine Continuous.mul ?_ (continuous_finsetProd _ fun l _ => ?_)
        · refine continuous_ofReal_cpow (f := fun p : ℝ × (Fin m → ℝ) => partialSq p.2 m + p.1 ^ 2)
            (((continuous_partialSq m).comp continuous_snd).add
            (continuous_fst.pow 2)) (fun p => ?_) β
          have := partialSq_pos p.2 m
          positivity
        · exact continuous_ofReal_cpow
            (f := fun p : ℝ × (Fin m → ℝ) => partialSq p.2 ((l : ℕ) + 1))
            ((continuous_partialSq _).comp continuous_snd)
            (fun p => partialSq_pos p.2 _) _
      -- the inner integral over the last coordinate
      have hinner : ∀ y : Fin m → ℝ, ∫ t : ℝ, H (t, y) =
          lineIntegral β * partialSqProd d' (β + 1 / 2) y := by
        intro y
        simp only [hHdef]
        rw [integral_mul_const, integral_add_sq_cpow (partialSq_pos y m), partialSqProd]
        ring
      have hnorm : ∀ y : Fin m → ℝ, ∫ t : ℝ, ‖H (t, y)‖ =
          (∫ s : ℝ, (1 + s ^ 2) ^ β.re) * ‖partialSqProd d' (β + 1 / 2) y‖ := by
        intro y
        have hnn : ∀ t : ℝ, ‖H (t, y)‖ = (partialSq y m + t ^ 2) ^ β.re *
            ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ (d' l).re := by
          intro t
          have hpos : 0 < partialSq y m + t ^ 2 := by
            have := partialSq_pos y m
            positivity
          simp only [hHdef]
          rw [norm_mul, norm_prod, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
          congr 1
          exact Finset.prod_congr rfl fun l _ =>
            Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos y _) _
        simp only [hnn]
        rw [integral_mul_const, integral_add_sq_rpow (partialSq_pos y m), norm_partialSqProd]
        simp only [Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im,
          Complex.re_ofNat, Complex.im_ofNat]
        norm_num
        ring
      have hHi : Integrable H (volume.prod volume) := by
        rw [integrable_prod_iff' hHc.aestronglyMeasurable]
        refine ⟨ae_of_all _ fun y => ?_, ?_⟩
        · simp only [hHdef]
          exact (integrable_add_sq_cpow (partialSq_pos y m) hβ).mul_const _
        · simp only [hnorm]
          exact hIHi.norm.const_mul _
      have hint : Integrable (partialSqProd d c) := by
        refine (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mp ?_
        rw [key, Measure.volume_eq_prod]
        exact hHi
      refine ⟨hint, ?_⟩
      have hval : ∫ x, partialSqProd d c x = lineIntegral β * ∫ y, partialSqProd d' (β + 1 / 2) y := by
        rw [← hmp.symm.integral_comp' (partialSqProd d c)]
        have : (fun p : ℝ × (Fin m → ℝ) => partialSqProd d c (e.symm p)) = H := key
        rw [this, Measure.volume_eq_prod, integral_prod_symm H hHi]
        simp only [hinner]
        rw [integral_const_mul]
      rw [hval]
      exact mul_ne_zero (lineIntegral_ne_zero hβ) hIHn

/-- The case `c = 0`: `∫_{ℝ^m} ∏_l r_{l+1}(x)^{d_l} dx` converges and does not vanish when
`∑_{l ≥ j} (Re d_l + 1/2) < 0` for every `j`. -/
theorem integrable_and_integral_prod_ne_zero {m : ℕ} {d : Fin m → ℂ} (hd : TailCondition d 0) :
    Integrable (fun x : Fin m → ℝ => ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ d l) ∧
      ∫ x : Fin m → ℝ, ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ d l ≠ 0 := by
  have h := integrable_and_integral_ne_zero m d 0 hd
  have hG : partialSqProd d 0 =
      fun x : Fin m → ℝ => ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ d l :=
    funext fun x => by simp [partialSqProd]
  rw [hG] at h
  exact h

end PartialSqIntegral

end Langlands.Archimedean
