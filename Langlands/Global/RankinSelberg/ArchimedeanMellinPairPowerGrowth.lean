import Langlands.Global.RankinSelberg.ArchimedeanMellinPairStripGrowth

/-! # Entire normalizations from a Mellin pair with a power Gaussian factor

See the paired Markdown file.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter MeasureTheory Set

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

open LocalFactor LocalFactor.Archimedean

/-- Strip growth is preserved by the reflection `s ↦ 1 - s`. -/
theorem _root_.Langlands.LocalFactor.Archimedean.HasStripExponentialGrowth.comp_one_sub {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) :
    HasStripExponentialGrowth (fun s => f (1 - s)) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hB⟩ := hf (1 - b) (1 - a)
  refine ⟨C, K, T, hC, hK, fun s ha hb ht => ?_⟩
  have him : |(1 - s).im| = |s.im| := by simp
  have h := hB (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith) (him.symm ▸ ht)
  rwa [him] at h

/-- Strip growth is preserved by finite products. -/
theorem _root_.Langlands.LocalFactor.Archimedean.HasStripExponentialGrowth.finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ j ∈ S, HasStripExponentialGrowth (f j)) :
    HasStripExponentialGrowth (fun z => ∏ j ∈ S, f j z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using HasStripExponentialGrowth.const 1
  | @insert j S hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hf j (Finset.mem_insert_self j S)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem line_bound_of_tail {f : ℂ → ℂ} (hf : Continuous f) (a : ℝ)
    {C K T : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (h : ∀ s : ℂ, s.re = a → T ≤ |s.im| → ‖f s‖ ≤ C * Real.exp (K * |s.im|)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, s.re = a → ‖f s‖ ≤ D * Real.exp (K * |s.im|) := by
  let B := max T 0
  let g (y : ℝ) := ‖f (⟨a, y⟩ : ℂ)‖
  have hg : Continuous g := by
    have hc : Continuous (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
    have he (y : ℝ) : (⟨a, y⟩ : ℂ) = (a : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    simpa only [g, he, Function.comp_apply] using (hf.comp hc).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.image (f := g) hg (s := Icc (-B) B)).bddAbove
  refine ⟨max C M, hC.trans (le_max_left _ _), fun s hs => ?_⟩
  by_cases hT : T ≤ |s.im|
  · exact (h s hs hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hsmall : s.im ∈ Icc (-B) B :=
      abs_le.mp ((lt_of_not_ge hT).le.trans (le_max_left _ _))
    have heq : (⟨a, s.im⟩ : ℂ) = s := Complex.ext hs.symm rfl
    have hnorm : ‖f s‖ ≤ M := by simpa only [g, heq] using hM (mem_image_of_mem g hsmall)
    exact (hnorm.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right (hC.trans (le_max_left _ _))
        (Real.one_le_exp (mul_nonneg hK (abs_nonneg s.im))))

private theorem norm_mellin_neg_le_strip {φ : ℝ → ℂ} (hφ : RapidDecay φ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin φ (-s)‖ ≤ C := by
  obtain ⟨C₀, h₀⟩ := hφ (b + 1)
  obtain ⟨C₁, h₁⟩ := hφ (a - 1)
  have hC₀ := RapidDecay.nonneg_const h₀
  have hC₁ := RapidDecay.nonneg_const h₁
  let w (t : ℝ) := if t ≤ 1 then C₀ else C₁ * t ^ (-2 : ℝ)
  have hw : IntegrableOn w (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    apply IntegrableOn.union
    · refine (integrableOn_const (C := C₀) (by simp : volume (Ioc (0 : ℝ) 1) ≠ ⊤)).congr_fun
        (fun t ht => ?_) measurableSet_Ioc
      simp [w, ht.2]
    · have hi : IntegrableOn (fun t : ℝ => C₁ * t ^ (-2 : ℝ)) (Ioi 1) :=
        ((integrableOn_Ioi_rpow_iff (s := -2) one_pos).2 (by norm_num)).const_mul C₁
      exact hi.congr_fun (fun t (ht : 1 < t) => by simp [w, not_le.mpr ht]) measurableSet_Ioi
  have hnonneg (t : ℝ) : 0 ≤ w t := by
    dsimp only [w]
    split_ifs with ht
    · exact hC₀
    · exact mul_nonneg hC₁ (Real.rpow_nonneg ((zero_lt_one.trans (lt_of_not_ge ht)).le) _)
  refine ⟨∫ t in Ioi (0 : ℝ), w t, integral_nonneg hnonneg, fun s ha hb => ?_⟩
  refine norm_integral_le_of_norm_le hw ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  change ‖(t : ℂ) ^ (-s - 1) • φ t‖ ≤ w t
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.neg_re,
    Complex.one_re]
  by_cases h : t ≤ 1
  · simp only [w, ite_eq_left h]
    calc
      _ ≤ t ^ (-b - 1) * (C₀ * t ^ (b + 1)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)) (h₀ t ht)
        (norm_nonneg _) (Real.rpow_nonneg ht.le _)
      _ = C₀ := by
        rw [mul_left_comm, ← Real.rpow_add ht, show -b - 1 + (b + 1) = 0 by ring,
          Real.rpow_zero, mul_one]
  · simp only [w, ite_eq_right h]
    calc
      _ ≤ t ^ (-a - 1) * (C₁ * t ^ (a - 1)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith)) (h₁ t ht)
        (norm_nonneg _) (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add ht, show -a - 1 + (a - 1) = -2 by ring]

private theorem norm_scale_mellin_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (F : X → ℂ) (δ : X → ℝ) (hδ : ∀ x, 0 < δ x) {s : ℂ}
    (h : Integrable (fun x => ‖F x‖ * δ x ^ s.re) μ) :
    ‖∫ x, F x * (δ x : ℂ) ^ s ∂μ‖ ≤ ∫ x, ‖F x‖ * δ x ^ s.re ∂μ := by
  refine norm_integral_le_of_norm_le h (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x)]

private theorem exp_neg_sq_pow_mul_exp_sq_pow (p : ℕ) (s : ℂ) :
    Complex.exp (-(s ^ 2)) ^ p * Complex.exp (s ^ 2) ^ p = 1 := by
  rw [← mul_pow, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_pow]

private theorem norm_exp_neg_sq_pow_le (p : ℕ) (s : ℂ) :
    ‖Complex.exp (-(s ^ 2)) ^ p‖ ≤ Real.exp ((p : ℝ) * s.im ^ 2) := by
  rw [norm_pow, Complex.norm_exp, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p))
  rw [Complex.neg_re, pow_two, Complex.mul_re]
  nlinarith [sq_nonneg s.re]

/-- A Mellin pair whose two Mellin transforms are a common power of the Gaussian `exp(s²)`
times two functions `D` and `Dd` of exponential strip growth (one of them multiplied by a
nonzero constant `ε`) gives two entire functions of exponential strip growth. They agree on a
right half-plane with `D` and `Dd` times the two weighted integrals and satisfy the reflection
`Nd (1 - s) = ε * N s` at every point. -/
def MellinPairPowerNormalizedGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (δ : X → ℝ) (G : Y → ℂ) (δd : Y → ℝ)
    (h k : ℝ → ℂ) (N₀ : ℝ) (p : ℕ) (ε : ℂ) (D Dd : ℂ → ℂ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable G ν →
    Measurable δ → Measurable δd → (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    Measurable h → Measurable k → RapidDecay h → RapidDecay k →
    (∀ σ : ℝ, N₀ ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ) →
    (∀ σ : ℝ, N₀ ≤ σ → Integrable (fun y => ‖G y‖ * δd y ^ σ) ν) →
    (∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta ν G δd k a⁻¹) →
    ε ≠ 0 →
    (∀ s : ℂ, mellin h (-s) = ε * Complex.exp (s ^ 2) ^ p * D s) →
    (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) ^ p * Dd (1 - s)) →
    HasStripExponentialGrowth D → HasStripExponentialGrowth Dd →
    ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
      (∀ s : ℂ, N₀ ≤ s.re → N s = D s * ∫ x, F x * (δ x : ℂ) ^ s ∂μ) ∧
      (∀ s : ℂ, N₀ ≤ s.re → Nd s = Dd s * ∫ y, G y * (δd y : ℂ) ^ s ∂ν) ∧
      ∀ s : ℂ, Nd (1 - s) = ε * N s

theorem mellinPairPowerNormalizedGrowth : MellinPairPowerNormalizedGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F δ G δd h k N₀ p ε D Dd hF hG hδm hδdm hδ hδd hh hk hhdec hkdec
    hFN hGN hpair hε hMh hMk hD hDd
  obtain ⟨hΘ, hΘr, hΘl⟩ := mellin_theta_entire μ ν F δ G δd hF hG hδm hδdm hδ hδd h k
    hh hk hhdec hkdec N₀ hFN hGN hpair
  let Z (s : ℂ) := ∫ x, F x * (δ x : ℂ) ^ s ∂μ
  let Zd (s : ℂ) := ∫ y, G y * (δd y : ℂ) ^ s ∂ν
  let R (s : ℂ) := ε⁻¹ * Complex.exp (-(s ^ 2)) ^ p * mellin (theta μ F δ h) (-s)
  have hRa : Differentiable ℂ R :=
    ((differentiable_const _).mul ((Complex.differentiable_exp.comp
      (differentiable_id.pow 2).neg).pow p)).mul hΘ
  have hRight (s : ℂ) (hs : N₀ ≤ s.re) : R s = D s * Z s := by
    dsimp only [R]
    rw [hΘr s hs, hMh s]
    calc
      _ = (ε⁻¹ * ε) * (Complex.exp (-(s ^ 2)) ^ p * Complex.exp (s ^ 2) ^ p) * (D s * Z s) := by
        ring
      _ = _ := by rw [inv_mul_cancel₀ hε, exp_neg_sq_pow_mul_exp_sq_pow, one_mul, one_mul]
  have hLeft (s : ℂ) (hs : s.re ≤ 1 - N₀) : R s = ε⁻¹ * (Dd (1 - s) * Zd (1 - s)) := by
    dsimp only [R]
    rw [hΘl s hs, hMk s]
    calc
      _ = ε⁻¹ * (Complex.exp (-(s ^ 2)) ^ p * Complex.exp (s ^ 2) ^ p) *
          (Dd (1 - s) * Zd (1 - s)) := by ring
      _ = _ := by rw [exp_neg_sq_pow_mul_exp_sq_pow, mul_one]
  have hGauss (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ C * Real.exp ((p : ℝ) * s.im ^ 2) := by
    obtain ⟨C, hC, hB⟩ := norm_mellin_neg_le_strip
      (theta_rapidDecay μ ν F δ G δd hδ hδd hhdec hkdec hFN hGN hpair) a b
    refine ⟨‖ε⁻¹‖ * C, mul_nonneg (norm_nonneg _) hC, fun s ha hb => ?_⟩
    simp only [R, norm_mul]
    calc
      _ ≤ ‖ε⁻¹‖ * Real.exp ((p : ℝ) * s.im ^ 2) * C :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_exp_neg_sq_pow_le p s) (norm_nonneg _))
          (hB s ha hb) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hRline (b : ℝ) (hb : N₀ ≤ b) : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, s.re = b → ‖R s‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨C, K, T, hC, hK, hB⟩ := hD b b
    let B := ∫ x, ‖F x‖ * δ x ^ b ∂μ
    have hB0 : 0 ≤ B :=
      integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδ x).le _)
    have htail (s : ℂ) (hs : s.re = b) (ht : T ≤ |s.im|) :
        ‖R s‖ ≤ (C * B) * Real.exp (K * |s.im|) := by
      have hsN : N₀ ≤ s.re := hs.symm ▸ hb
      have hI := norm_scale_mellin_le F δ hδ (hFN s.re hsN)
      rw [hs] at hI
      rw [hRight s hsN, norm_mul]
      calc
        _ ≤ (C * Real.exp (K * |s.im|)) * B :=
          mul_le_mul (hB s hs.ge hs.le ht) hI (norm_nonneg _) (by positivity)
        _ = _ := by ring
    obtain ⟨M, hM, hMR⟩ := line_bound_of_tail hRa.continuous b (mul_nonneg hC hB0) hK htail
    exact ⟨M, K, hM, hK, hMR⟩
  have hLline (a : ℝ) (ha : a ≤ 1 - N₀) : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, s.re = a → ‖R s‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨C, K, T, hC, hK, hB⟩ := hDd (1 - a) (1 - a)
    let B := ∫ y, ‖G y‖ * δd y ^ (1 - a) ∂ν
    have hB0 : 0 ≤ B :=
      integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδd x).le _)
    have htail (s : ℂ) (hs : s.re = a) (ht : T ≤ |s.im|) :
        ‖R s‖ ≤ (‖ε⁻¹‖ * (C * B)) * Real.exp (K * |s.im|) := by
      have hre : (1 - s).re = 1 - a := by simp only [Complex.sub_re, Complex.one_re, hs]
      have him : |(1 - s).im| = |s.im| := by simp
      have hsN : N₀ ≤ (1 - s).re := by rw [hre]; linarith
      have hI := norm_scale_mellin_le G δd hδd (hGN (1 - s).re hsN)
      rw [hre] at hI
      have hB' := hB (1 - s) hre.ge hre.le (him.symm ▸ ht)
      rw [him] at hB'
      rw [hLeft s (hs.symm ▸ ha), norm_mul, norm_mul]
      calc
        _ ≤ ‖ε⁻¹‖ * ((C * Real.exp (K * |s.im|)) * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hB' hI (norm_nonneg _) (by positivity))
            (norm_nonneg _)
        _ = _ := by ring
    obtain ⟨U, hU, hUR⟩ := line_bound_of_tail hRa.continuous a
      (mul_nonneg (norm_nonneg _) (mul_nonneg hC hB0)) hK htail
    exact ⟨U, K, hU, hK, hUR⟩
  have hRg : HasStripExponentialGrowth R := by
    intro a b
    let l := min a (1 - N₀) - 1
    let r := max (max a b) N₀ + 1
    have hl : l < min a (1 - N₀) := sub_lt_self _ zero_lt_one
    have hr : max (max a b) N₀ < r := lt_add_one _
    have hla : l < a := hl.trans_le (min_le_left _ _)
    have har : a < r := ((le_max_left a b).trans (le_max_left _ _)).trans_lt hr
    have hbr : b < r := ((le_max_right a b).trans (le_max_left _ _)).trans_lt hr
    obtain ⟨Cl, Kl, _, _, hEl⟩ := hLline l (hl.le.trans (min_le_right _ _))
    obtain ⟨Cr, Kr, _, _, hEr⟩ := hRline r ((le_max_right _ _).trans hr.le)
    obtain ⟨Cq, hCq, hQ⟩ := hGauss l r
    let C := max Cq (max Cl Cr)
    let K := max Kl Kr
    have hC : 0 ≤ C := hCq.trans (le_max_left _ _)
    refine ⟨C * Real.exp ((|l| + |r|) ^ 2), K ^ 2 + 1, 1, by positivity, by positivity,
      fun s ha hb ht => ?_⟩
    apply norm_le_exp_of_gaussian_on_strip hRa (hla.trans har) hC (Nat.cast_nonneg p)
      (fun w hw hw' => ?_) (fun w hw => ?_) (hla.le.trans ha) (hb.trans hbr.le) ht
    · exact (hQ w hw hw').trans
        (mul_le_mul_of_nonneg_right (le_max_left Cq (max Cl Cr)) (Real.exp_pos _).le)
    · rcases hw with hw | hw
      · exact (hEl w hw).trans (mul_le_mul ((le_max_left Cl Cr).trans (le_max_right _ _))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
          (Real.exp_pos _).le hC)
      · exact (hEr w hw).trans (mul_le_mul ((le_max_right Cl Cr).trans (le_max_right _ _))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
          (Real.exp_pos _).le hC)
  refine ⟨R, fun t => ε * R (1 - t), hRa,
    (differentiable_const ε).mul (hRa.comp (differentiable_const 1 |>.sub differentiable_id)),
    hRg, hRg.comp_one_sub.const_mul ε, hRight, fun t ht => ?_, fun s => ?_⟩
  · have hre : (1 - t).re ≤ 1 - N₀ := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    change ε * R (1 - t) = Dd t * Zd t
    rw [hLeft (1 - t) hre, sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  · change ε * R (1 - (1 - s)) = ε * R s
    rw [sub_sub_cancel]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair
