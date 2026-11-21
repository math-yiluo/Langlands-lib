import Langlands.LocalFactor.ArchimedeanPairFactor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Growth of the archimedean Gamma denominators in vertical strips -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter MeasureTheory Set
open scoped Topology

namespace Langlands.LocalFactor.Archimedean

/-- A function is bounded by an exponential in the absolute imaginary part on each vertical
strip for sufficiently large absolute imaginary part. -/
def HasStripExponentialGrowth (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C K T : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖f s‖ ≤ C * Real.exp (K * |s.im|)

private theorem norm_Gamma_le_real (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1)
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- The Gamma integral bounds the complex Gamma function on any closed strip in the
positive half-plane. -/
theorem norm_Gamma_le_on_strip {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Complex.Gamma s‖ ≤ C := by
  have hGc : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    have hnonpole (n : ℕ) : (x : ℂ) ≠ -(n : ℂ) := by
      intro hn
      have he := congrArg Complex.re hn
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at he
      linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
    have hc := (Complex.continuousAt_Gamma (x : ℂ) hnonpole).comp Complex.continuous_ofReal.continuousAt
    exact (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hGc).bddAbove
  refine ⟨max 0 M, le_max_left _ _, fun s hs hs' => ?_⟩
  exact (norm_Gamma_le_real s (ha.trans_le hs)).trans
    ((hM (mem_image_of_mem _ ⟨hs, hs'⟩)).trans (le_max_right _ _))

private theorem norm_Gamma_le_add_nat_of_one_le_abs_im (s : ℂ) (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖s + (n : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (s + (n : ℂ))
      simp only [Complex.add_im, Complex.natCast_im, add_zero] at h
      exact hs.trans h
    have hnz : s + (n : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hn))
    apply ih.trans
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hnz, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hn

private theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  have h₂ : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp, Complex.mul_I_re]
    exact Real.exp_le_exp.mpr (neg_le_abs _)
  exact (div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (by norm_num)).trans
    (by ring_nf; exact le_rfl)

private theorem inv_Gamma_eq_reflection (s : ℂ) (hs : s.im ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin ((Real.pi : ℂ) * s) / Real.pi := by
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hi := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
      Complex.intCast_im, mul_zero, zero_mul, add_zero] at hi
    exact hs ((mul_eq_zero.mp hi).resolve_left Real.pi_ne_zero)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := Complex.Gamma_mul_Gamma_one_sub s
  have hΓ : Complex.Gamma s ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact (div_ne_zero hπ hsin) h.symm
  apply (mul_left_cancel₀ hΓ)
  rw [mul_inv_cancel₀ hΓ, ← mul_div_assoc, ← mul_assoc, h]
  field_simp

/-- The exponent `π` in the large-imaginary-part estimate is independent of the real strip. -/
theorem norm_inv_Gamma_le_exp_of_one_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨N, hN⟩ := exists_nat_gt b
  have hpos : 0 < 1 - b + (N : ℝ) := by linarith
  obtain ⟨C, hC, hΓ⟩ := norm_Gamma_le_on_strip (b := 1 - a + (N : ℝ)) hpos
  refine ⟨C / Real.pi, div_nonneg hC Real.pi_pos.le, ?_⟩
  intro s hlo hhi hs
  have hsim : s.im ≠ 0 := by intro h; norm_num [h] at hs
  have him : 1 ≤ |(1 - s).im| := by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hs
  have hre : (1 - s + (N : ℂ)).re = 1 - s.re + N := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.natCast_re]
  have hbound := (norm_Gamma_le_add_nat_of_one_le_abs_im (1 - s) him N).trans
    (hΓ (1 - s + (N : ℂ)) (by rw [hre]; linarith) (by rw [hre]; linarith))
  have hs' : ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos Real.pi_pos] using norm_sin_le_exp_abs_im ((Real.pi : ℂ) * s)
  change ‖(Complex.Gamma s)⁻¹‖ ≤ _
  rw [inv_Gamma_eq_reflection s hsim, norm_div, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ C * Real.exp (Real.pi * |s.im|) / Real.pi := by
      exact div_le_div_of_nonneg_right (mul_le_mul hbound hs' (norm_nonneg _) hC) Real.pi_pos.le
    _ = _ := by ring

/-- Euler reflection and a shift of the Gamma integral give an exponential bound for the
entire reciprocal Gamma function on each vertical strip. -/
theorem hasStripExponentialGrowth_inv_Gamma : HasStripExponentialGrowth (fun s => (Complex.Gamma s)⁻¹) := by
  intro a b
  obtain ⟨C, hC, h⟩ := norm_inv_Gamma_le_exp_of_one_le a b
  exact ⟨C, Real.pi, 1, hC, Real.pi_pos.le, h⟩

/-- The complex reciprocal Gamma block has rate `π` on each closed vertical strip. -/
theorem norm_gammaComplex_denominator_le_exp (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖gammaComplex.denominator s‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC, h⟩ := norm_inv_Gamma_le_exp_of_one_le a b
  let R := max |a| |b| + 1
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (gammaComplex.entire.continuous.continuousOn)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.one_le_pi_div_two]
  let A := C * (2 * Real.pi) ^ b / 2
  refine ⟨max (max B 0) A, (le_max_right B 0).trans (le_max_left _ _), fun s hs ht => ?_⟩
  by_cases hi : 1 ≤ |s.im|
  · change ‖(Complex.Gammaℂ s)⁻¹‖ ≤ _
    rw [Complex.Gammaℂ_def, mul_inv_rev, mul_inv_rev, Complex.cpow_neg, inv_inv,
      norm_mul, norm_mul, norm_inv (2 : ℂ), Complex.norm_ofNat,
      show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hπ)]
    have hg : ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|) := h s hs ht hi
    have hp := Real.rpow_le_rpow_of_exponent_le hπ ht
    calc
      _ ≤ (C * Real.exp (Real.pi * |s.im|)) * ((2 * Real.pi) ^ b * (2 : ℝ)⁻¹) := by gcongr
      _ = A * Real.exp (Real.pi * |s.im|) := by dsimp only [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hr : |s.re| ≤ max |a| |b| := abs_le.mpr
      ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hs),
        ht.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    have hsR : s ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr <|
      (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hr (le_of_not_ge hi))
    exact (hB s hsR).trans <| (le_max_left B 0).trans <|
      (le_max_left (max B 0) A).trans <| le_mul_of_one_le_right
        ((le_max_right B 0).trans (le_max_left _ _)) (Real.one_le_exp (by positivity))

/-- Strip growth is preserved by multiplication. -/
theorem HasStripExponentialGrowth.mul {f g : ℂ → ℂ}
    (hf : HasStripExponentialGrowth f) (hg : HasStripExponentialGrowth g) :
    HasStripExponentialGrowth (f * g) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf a b
  obtain ⟨D, L, U, hD, hL, hg⟩ := hg a b
  refine ⟨C * D, K + L, max T U, mul_nonneg hC hD, add_nonneg hK hL, ?_⟩
  intro s ha hb hs
  rw [Pi.mul_apply, norm_mul, add_mul, Real.exp_add]
  calc
    _ ≤ (C * Real.exp (K * |s.im|)) * (D * Real.exp (L * |s.im|)) := by
      exact mul_le_mul (hf s ha hb ((le_max_left _ _).trans hs))
        (hg s ha hb ((le_max_right _ _).trans hs)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem stripGrowth_const (c : ℂ) : HasStripExponentialGrowth (fun _ => c) := by
  intro a b
  exact ⟨‖c‖, 0, 0, norm_nonneg c, le_rfl, fun s _ _ _ => by simp⟩

/-- Strip growth is preserved by translation and positive real dilation of the argument. -/
theorem HasStripExponentialGrowth.div_add {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f)
    (d : ℂ) {c : ℝ} (hc : 0 < c) : HasStripExponentialGrowth (fun s => f ((s + d) / c)) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf ((a + d.re) / c) ((b + d.re) / c)
  refine ⟨C * Real.exp ((K / c) * |d.im|), K / c, c * T + |d.im|, by positivity, by positivity, ?_⟩
  intro s ha hb hs
  have hlower : T ≤ |((s + d) / (c : ℂ)).im| := by
    rw [Complex.div_ofReal_im, Complex.add_im, abs_div, abs_of_pos hc, le_div_iff₀ hc]
    have h := abs_add_le (s.im + d.im) (-d.im)
    rw [add_neg_cancel_right, abs_neg] at h
    linarith
  have hUpper : K * |((s + d) / (c : ℂ)).im| ≤ (K / c) * |d.im| + (K / c) * |s.im| := by
    rw [Complex.div_ofReal_im, Complex.add_im, abs_div, abs_of_pos hc]
    calc
      _ = (K / c) * |s.im + d.im| := by ring
      _ ≤ (K / c) * (|s.im| + |d.im|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (div_nonneg hK hc.le)
      _ = _ := by ring
  calc
    ‖f ((s + d) / (c : ℂ))‖ ≤ C * Real.exp (K * |((s + d) / (c : ℂ)).im|) :=
      hf _ (by rw [Complex.div_ofReal_re, Complex.add_re]; gcongr)
        (by rw [Complex.div_ofReal_re, Complex.add_re]; gcongr) hlower
    _ ≤ C * Real.exp ((K / c) * |d.im| + (K / c) * |s.im|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hUpper) hC
    _ = _ := by rw [Real.exp_add, mul_assoc]

private theorem stripGrowth_cpow (p : ℝ) (hp : 1 ≤ p) :
    HasStripExponentialGrowth (fun s => (p : ℂ) ^ s) := by
  intro a b
  refine ⟨p ^ b, 0, 0, by positivity, le_rfl, fun s _ hsb _ => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hp), zero_mul, Real.exp_zero, mul_one]
  exact Real.rpow_le_rpow_of_exponent_le hp hsb

private theorem stripGrowth_gammaReal : HasStripExponentialGrowth gammaReal.denominator := by
  have hΓ := hasStripExponentialGrowth_inv_Gamma.div_add 0 (c := 2) (by norm_num)
  have hπ := (stripGrowth_cpow Real.pi (by linarith [Real.one_le_pi_div_two])).div_add 0
    (c := 2) (by norm_num)
  have heq : gammaReal.denominator =
      (fun s : ℂ => (Complex.Gamma (s / 2))⁻¹) * (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) := by
    funext s
    change (Complex.Gammaℝ s)⁻¹ = _
    rw [Complex.Gammaℝ_def, mul_inv_rev, show -s / 2 = -(s / 2) by ring,
      Complex.cpow_neg, inv_inv, Pi.mul_apply]
  rw [heq]
  simpa only [add_zero, Complex.ofReal_ofNat] using hΓ.mul hπ

private theorem stripGrowth_gammaComplex : HasStripExponentialGrowth gammaComplex.denominator := by
  have hπ := stripGrowth_cpow (2 * Real.pi) (by linarith [Real.one_le_pi_div_two])
  have heq : gammaComplex.denominator = (fun s : ℂ => (Complex.Gamma s)⁻¹) *
      ((fun s : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ s) * fun _ : ℂ => (2 : ℂ)⁻¹) := by
    funext s
    change (Complex.Gammaℂ s)⁻¹ = _
    simp only [Complex.Gammaℂ_def, Pi.mul_apply, mul_inv_rev, Complex.cpow_neg,
      inv_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [heq]
  exact hasStripExponentialGrowth_inv_Gamma.mul (hπ.mul (stripGrowth_const (2 : ℂ)⁻¹))

/-- The denominator of each shifted archimedean Gamma block has exponential growth on
vertical strips. -/
theorem GammaBlock.stripGrowth_denominator (b : GammaBlock) :
    HasStripExponentialGrowth b.factor.denominator := by
  cases b with
  | real d =>
    change HasStripExponentialGrowth (fun s => gammaReal.denominator (s + d))
    simpa only [Complex.ofReal_one, div_one] using
      stripGrowth_gammaReal.div_add d (c := 1) one_pos
  | complex d =>
    change HasStripExponentialGrowth (fun s => gammaComplex.denominator (s + d))
    simpa only [Complex.ofReal_one, div_one] using
      stripGrowth_gammaComplex.div_add d (c := 1) one_pos

/-- A finite product of Gamma blocks preserves the strip growth bound. -/
theorem stripGrowth_gammaProduct_denominator (bs : List GammaBlock) :
    HasStripExponentialGrowth (gammaProduct bs).denominator := by
  induction bs with
  | nil => exact stripGrowth_const 1
  | cons b bs ih =>
    change HasStripExponentialGrowth (b.factor.denominator * (gammaProduct bs).denominator)
    exact b.stripGrowth_denominator.mul ih

/-- The real pair L-denominator has at most exponential growth in vertical strips. -/
theorem stripGrowth_realPairLFactor_denominator (xs ys : List RealBlock) :
    HasStripExponentialGrowth (realPairLFactor xs ys).denominator := by
  rw [realPairLFactor, realLFactor_eq_gammaProduct]
  exact stripGrowth_gammaProduct_denominator _

/-- The complex pair L-denominator has at most exponential growth in vertical strips. -/
theorem stripGrowth_complexPairLFactor_denominator (xs ys : List ComplexCharacterData) :
    HasStripExponentialGrowth (complexPairLFactor xs ys).denominator := by
  rw [complexPairLFactor, complexLFactor_eq_gammaProduct]
  exact stripGrowth_gammaProduct_denominator _

namespace HasStripExponentialGrowth

/-- Constant functions have exponential strip growth. -/
theorem const (c : ℂ) : HasStripExponentialGrowth (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩

/-- The sum of two functions of exponential strip growth has the same property. -/
theorem add {f g : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (hg : HasStripExponentialGrowth g) :
    HasStripExponentialGrowth (f + g) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf a b
  obtain ⟨D, L, S, hD, hL, hg⟩ := hg a b
  refine ⟨C + D, max K L, max T S, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro s hs ht hw
  have hMax (k : ℝ) (hk : k ≤ max K L) :
      Real.exp (k * |s.im|) ≤ Real.exp (max K L * |s.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk (abs_nonneg _))
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    ((hf s hs ht ((le_max_left _ _).trans hw)).trans
      (mul_le_mul_of_nonneg_left (hMax K (le_max_left _ _)) hC))
    ((hg s hs ht ((le_max_right _ _).trans hw)).trans
      (mul_le_mul_of_nonneg_left (hMax L (le_max_right _ _)) hD)))

/-- Multiplication by a fixed complex scalar preserves exponential strip growth. -/
theorem const_mul {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (c : ℂ) :
    HasStripExponentialGrowth (fun s => c * f s) :=
  (const c).mul hf

/-- A finite sum of functions of exponential strip growth has the same property. -/
theorem fun_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ j ∈ s, HasStripExponentialGrowth (f j)) :
    HasStripExponentialGrowth (fun z => ∑ j ∈ s, f j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end HasStripExponentialGrowth

end Langlands.LocalFactor.Archimedean
