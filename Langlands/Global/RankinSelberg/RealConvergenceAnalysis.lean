import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Pi

/-! # Analytic lemmas for the convergence of real Rankin–Selberg integrals -/

noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis

/-! ### Holomorphy of exponential families of integrals -/

theorem abs_mul_exp_le {ℓ t t₀ δ : ℝ} (hδ : 0 < δ) (ht : |t - t₀| ≤ δ) :
    |ℓ| * Real.exp (t * ℓ) ≤
      (Real.exp ((t₀ + 2 * δ) * ℓ) + Real.exp ((t₀ - 2 * δ) * ℓ)) / δ := by
  rw [le_div_iff₀ hδ]
  have h1 : δ * |ℓ| ≤ Real.exp (δ * |ℓ|) := by
    have := Real.add_one_le_exp (δ * |ℓ|)
    linarith
  have h2 : Real.exp (t * ℓ) * Real.exp (δ * |ℓ|) ≤
      Real.exp ((t₀ + 2 * δ) * ℓ) + Real.exp ((t₀ - 2 * δ) * ℓ) := by
    rw [← Real.exp_add]
    rcases le_total 0 ℓ with hℓ | hℓ
    · rw [abs_of_nonneg hℓ]
      have hle : t * ℓ + δ * ℓ ≤ (t₀ + 2 * δ) * ℓ := by
        have : t ≤ t₀ + δ := by linarith [le_abs_self (t - t₀)]
        nlinarith
      exact (Real.exp_le_exp.mpr hle).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos hℓ]
      have hle : t * ℓ + δ * -ℓ ≤ (t₀ - 2 * δ) * ℓ := by
        have : t₀ - δ ≤ t := by linarith [neg_abs_le (t - t₀)]
        nlinarith
      exact (Real.exp_le_exp.mpr hle).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  calc
    |ℓ| * Real.exp (t * ℓ) * δ = Real.exp (t * ℓ) * (δ * |ℓ|) := by ring
    _ ≤ Real.exp (t * ℓ) * Real.exp (δ * |ℓ|) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ _ := h2

theorem norm_cexp_mul_ofReal (s : ℂ) (x : ℝ) :
    ‖Complex.exp (s * (x : ℂ))‖ = Real.exp (s.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **Holomorphy of exponential families.** If `‖f‖ · exp(t ℓ)` is integrable for every real
`t > σ`, then `s ↦ ∫ f · exp(s ℓ)` is holomorphic on the half-plane `Re s > σ`. -/
theorem differentiableOn_integral_cexp_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} {ℓ : X → ℝ} {σ : ℝ} (hf : AEStronglyMeasurable f μ)
    (hℓ : AEStronglyMeasurable ℓ μ)
    (hint : ∀ t : ℝ, σ < t → Integrable (fun x => ‖f x‖ * Real.exp (t * ℓ x)) μ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, f x * Complex.exp (s * (ℓ x : ℂ)) ∂μ)
      {s : ℂ | σ < s.re} := by
  intro s₀ hs₀
  have hs₀' : σ < s₀.re := hs₀
  set δ := (s₀.re - σ) / 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hℓc : AEStronglyMeasurable (fun x => (ℓ x : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hℓ
  have hexpm : ∀ s : ℂ, AEStronglyMeasurable (fun x => Complex.exp (s * (ℓ x : ℂ))) μ :=
    fun s => Complex.continuous_exp.comp_aestronglyMeasurable (hℓc.const_mul s)
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => f x * Complex.exp (s * (ℓ x : ℂ))) μ :=
    fun s => hf.mul (hexpm s)
  have hderiv : ∀ x (s : ℂ), HasDerivAt (fun s => f x * Complex.exp (s * (ℓ x : ℂ)))
      (f x * ((ℓ x : ℂ) * Complex.exp (s * (ℓ x : ℂ)))) s := by
    intro x s
    have h := (((hasDerivAt_id' s).mul_const (ℓ x : ℂ)).cexp).const_mul (f x)
    convert h using 1
    ring
  let bound : X → ℝ := fun x =>
    (‖f x‖ * Real.exp ((s₀.re + 2 * δ) * ℓ x) + ‖f x‖ * Real.exp ((s₀.re - 2 * δ) * ℓ x)) / δ
  have hbound_int : Integrable bound μ :=
    ((hint _ (by linarith)).add (hint _ (by linarith))).div_const δ
  have hF₀ : Integrable (fun x => f x * Complex.exp (s₀ * (ℓ x : ℂ))) μ := by
    refine (hint s₀.re hs₀').mono' (hmeas s₀) (ae_of_all _ fun x => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal]
  have h_bound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball s₀ δ,
      ‖f x * ((ℓ x : ℂ) * Complex.exp (s * (ℓ x : ℂ)))‖ ≤ bound x := by
    refine ae_of_all _ fun x s hs => ?_
    have hre : |s.re - s₀.re| ≤ δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hs
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hs.le
    have h := abs_mul_exp_le (ℓ := ℓ x) hδ hre
    calc
      ‖f x * ((ℓ x : ℂ) * Complex.exp (s * (ℓ x : ℂ)))‖ =
          ‖f x‖ * (|ℓ x| * Real.exp (s.re * ℓ x)) := by
        rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖f x‖ * ((Real.exp ((s₀.re + 2 * δ) * ℓ x) +
          Real.exp ((s₀.re - 2 * δ) * ℓ x)) / δ) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = bound x := by
        simp only [bound]
        ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀)
    (F := fun s x => f x * Complex.exp (s * (ℓ x : ℂ)))
    (F' := fun s x => f x * ((ℓ x : ℂ) * Complex.exp (s * (ℓ x : ℂ))))
    (bound := bound) (Metric.ball_mem_nhds s₀ hδ) (Filter.Eventually.of_forall fun s => hmeas s)
    hF₀ (hf.mul (hℓc.mul (hexpm s₀))) h_bound hbound_int
    (ae_of_all _ fun x s _ => hderiv x s)
  exact key.2.differentiableAt.differentiableWithinAt

/-! ### Integrability of `exp(-c ∑ |x_j|)` -/

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos (mem_Ioi.mp hx)]
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hc 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    ring_nf
  have h := h2.union h1
  rw [Iic_union_Ioi, integrableOn_univ] at h
  exact h

theorem integrable_exp_neg_mul_sum_abs {n : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-c * ∑ j, |x j|)) := by
  have h := Integrable.fintype_prod (f := fun (_ : Fin n) (t : ℝ) => Real.exp (-c * |t|))
    (μ := fun _ => volume) fun _ => integrable_exp_neg_mul_abs hc
  rw [← volume_pi] at h
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [Finset.mul_sum, Real.exp_sum]

theorem lintegral_exp_neg_mul_sum_abs_lt_top {n : ℕ} {c : ℝ} (hc : 0 < c) :
    ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (-c * ∑ j, |x j|)) < ⊤ := by
  have h := (integrable_exp_neg_mul_sum_abs (n := n) hc).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)] at h
  exact h

/-! ### Simple-root coordinates -/

variable {r : ℕ}

/-- The sum of the positive parts of the simple-root coordinates `y_i - y_(i+1)`. -/
def rootPos (y : Fin (r + 1) → ℝ) : ℝ :=
  ∑ i : Fin r, max (y i.castSucc - y i.succ) 0

theorem rootPos_nonneg (y : Fin (r + 1) → ℝ) : 0 ≤ rootPos y :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem sum_root_eq (y : Fin (r + 1) → ℝ) :
    ∑ i : Fin r, (y i.castSucc - y i.succ) = rootPos y - rootPos (-y) := by
  unfold rootPos
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, ← neg_sub (y i.castSucc),
    max_zero_sub_max_neg_zero_eq_self]

theorem sub_last_le_partial (y : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    y j - y (Fin.last r) ≤
      ∑ i : Fin r, if j ≤ i.castSucc then max (y i.castSucc - y i.succ) 0 else 0 := by
  induction j using Fin.reverseInduction with
  | last =>
    rw [sub_self]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp
  | cast i₀ ih =>
    have hterm : ∀ i : Fin r,
        (if i₀.castSucc ≤ i.castSucc then max (y i.castSucc - y i.succ) 0 else 0) =
          (if i = i₀ then max (y i.castSucc - y i.succ) 0 else 0) +
            (if i₀.succ ≤ i.castSucc then max (y i.castSucc - y i.succ) 0 else 0) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        have hn : ¬ i.succ ≤ i.castSucc := by
          rw [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
          omega
        simp [hn]
      · simp only [hi, ↓reduceIte, zero_add]
        have hiff : i₀.castSucc ≤ i.castSucc ↔ i₀.succ ≤ i.castSucc := by
          rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_castSucc,
            Fin.val_succ]
          have : i.val ≠ i₀.val := fun h => hi (Fin.ext h)
          omega
        by_cases h : i₀.succ ≤ i.castSucc
        · simp only [hiff.mpr h, h, ↓reduceIte]
        · simp only [mt hiff.mp h, h, ↓reduceIte]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    have hle : y i₀.castSucc - y i₀.succ ≤ max (y i₀.castSucc - y i₀.succ) 0 := le_max_left _ _
    linarith

theorem sub_last_le (y : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    y j - y (Fin.last r) ≤ rootPos y := by
  refine (sub_last_le_partial y j).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem last_sub_le (y : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    y (Fin.last r) - y j ≤ rootPos (-y) := by
  have h := sub_last_le (-y) j
  rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg] at h
  exact h

theorem sum_sub_last_le (y : Fin (r + 1) → ℝ) :
    ∑ j, (y j - y (Fin.last r)) ≤ ((r : ℝ) + 1) * rootPos y - rootPos (-y) := by
  rw [Fin.sum_univ_castSucc, sub_self, add_zero]
  have h1 : ∀ i : Fin r, y i.castSucc - y (Fin.last r) ≤
      (y i.castSucc - y i.succ) + rootPos y := fun i => by
    have := sub_last_le y i.succ
    linarith
  calc
    ∑ i : Fin r, (y i.castSucc - y (Fin.last r)) ≤
        ∑ i : Fin r, ((y i.castSucc - y i.succ) + rootPos y) :=
      Finset.sum_le_sum fun i _ => h1 i
    _ = (rootPos y - rootPos (-y)) + r * rootPos y := by
      rw [Finset.sum_add_distrib, sum_root_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by ring

theorem sum_abs_le (y : Fin (r + 1) → ℝ) :
    ∑ j, |y j| ≤ ((r : ℝ) + 1) * (|y (Fin.last r)| + rootPos y + rootPos (-y)) := by
  have h : ∀ j, |y j| ≤ |y (Fin.last r)| + rootPos y + rootPos (-y) := fun j => by
    have h1 := sub_last_le y j
    have h2 := last_sub_le y j
    have h3 := rootPos_nonneg y
    have h4 := rootPos_nonneg (-y)
    rcases abs_cases (y j) with ⟨h5, h5'⟩ | ⟨h5, h5'⟩ <;>
      rcases abs_cases (y (Fin.last r)) with ⟨h6, h6'⟩ | ⟨h6, h6'⟩ <;> linarith
  calc
    ∑ j, |y j| ≤ ∑ _j : Fin (r + 1), (|y (Fin.last r)| + rootPos y + rootPos (-y)) :=
      Finset.sum_le_sum fun j _ => h j
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- **Exponent inequality.** Large decay `M` in the positive simple-root coordinates, large
decay `K` in the positive part of the last coordinate and a large determinant exponent `t`
dominate any fixed exponential growth `A ∑ |y_j|`. -/
theorem exponent_le (y : Fin (r + 1) → ℝ) {A t M K : ℝ} (hA : 0 ≤ A)
    (ht : (A + 1) * ((r : ℝ) + 1) ≤ t)
    (hM : (A + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1) ≤ M)
    (hK : (A + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1) ≤ K) :
    -M * rootPos y + A * ∑ j, |y j| + t * ∑ j, y j - K * max (y (Fin.last r)) 0 ≤
      -∑ j, |y j| := by
  set n : ℝ := (r : ℝ) + 1 with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  set m := y (Fin.last r)
  set P := rootPos y
  set Q := rootPos (-y)
  set S := ∑ j, |y j|
  have hP : 0 ≤ P := rootPos_nonneg y
  have hQ : 0 ≤ Q := rootPos_nonneg (-y)
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hsum : ∑ j, y j = n * m + ∑ j, (y j - m) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hn]
    push_cast
    ring
  have hS : S ≤ n * (|m| + P + Q) := sum_abs_le y
  have hD : ∑ j, (y j - m) ≤ n * P - Q := sum_sub_last_le y
  have h1 : P * ((A + 1) * n + t * n - M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP (by linarith)
  have h2 : Q * ((A + 1) * n - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ (by linarith)
  have h3 : (A + 1) * S ≤ (A + 1) * (n * (|m| + P + Q)) :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h4 : t * ∑ j, (y j - m) ≤ t * (n * P - Q) := mul_le_mul_of_nonneg_left hD ht0
  have h5 : (A + 1) * n * |m| + t * n * m - K * max m 0 ≤ 0 := by
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left hm]
      have : m * ((A + 1) * n + t * n - K) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hm (by linarith)
      linarith
    · rw [abs_of_nonpos hm, max_eq_right hm]
      have hAt : A + 1 ≤ t := le_trans (by nlinarith) ht
      have : (n * m) * (t - (A + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
      linarith
  rw [hsum]
  nlinarith [h1, h2, h3, h4, h5]

end Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis
