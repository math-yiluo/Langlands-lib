import Langlands.Analysis.SeveralComplex.CompactParameterEntireContinuation
import Langlands.Analysis.Complex.EntireStripExtension

/-! # Preservation of exponential strip growth under holomorphic parameter continuation -/

noncomputable section

open Filter Set Metric
open scoped Topology
open Langlands.Analysis (norm_le_of_exp_bounds_on_vertical_lines)
open Langlands.LocalFactor.Archimedean (HasStripExponentialGrowth)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SeveralComplex

private theorem coefficientDecay_uniform {I : Type*} [Nonempty I] (c : I → ℕ → ℂ → ℂ)
    (hc : ∀ i n, DifferentiableOn ℂ (c i n) (ball (0 : ℂ) 3))
    (hA : ∃ A : ℝ, ∀ i n z, z ∈ closedBall (0 : ℂ) 2 → ‖c i n z‖ ≤ A)
    (hSmall : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ∀ b > (0 : ℝ),
      ∀ᶠ n in atTop, ∀ i, ‖c i n z‖ ≤ b ^ n) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n in atTop, ∀ i z, z ∈ closedBall (0 : ℂ) (3 / 2) → ‖c i n z‖ ≤ b ^ n := by
  classical
  let Bad (n : ℕ) (i : I) := ∃ z ∈ closedBall (0 : ℂ) (3 / 2), b ^ n < ‖c i n z‖
  let pick (n : ℕ) : I := if h : ∃ i, Bad n i then h.choose else Classical.choice inferInstance
  obtain ⟨A, hA⟩ := hA
  obtain ⟨δ, hδ, hδ'⟩ := hSmall
  have h := holomorphicCoefficientDecay (fun n => c (pick n) n)
    (fun n => hc _ n) ⟨A, fun n z hz => hA _ n z hz⟩
    ⟨δ, hδ, fun z hz q hq => (hδ' z hz q hq).mono (fun n hn => hn (pick n))⟩ b hb
  filter_upwards [h] with n hn i z hz
  by_contra! he
  have hBad : ∃ i, Bad n i := ⟨i, z, hz, he⟩
  obtain ⟨w, hw, hlt⟩ := hBad.choose_spec
  have hp : pick n = hBad.choose := dite_eq_left hBad
  rw [← hp] at hlt
  exact (not_lt_of_ge (hn w hw)) hlt

private theorem halfPlane_ball_subset (σ : ℝ) :
    ball ((σ + 2 : ℝ) : ℂ) 2 ⊆ {s : ℂ | σ < s.re} := by
  intro w hw
  have hn := mem_ball_iff_norm.mp hw
  have habs := (Complex.abs_re_le_norm _).trans_lt hn
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  change σ < w.re
  linarith [(abs_lt.mp habs).1]

private theorem norm_weighted_translate_le {C K K' B T : ℝ} (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hKK' : K ≤ K') {s : ℂ} (hs : |s.im| ≤ B) {v : ℂ}
    (hv : ‖v‖ ≤ C * Real.exp (K * |(s + (T : ℂ) * Complex.I).im|)) :
    ‖(Real.exp (-K' * |T|) : ℂ) * v‖ ≤ C * Real.exp (K * B) := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans ?_
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have him : (s + (T : ℂ) * Complex.I).im = s.im + T := by simp [Complex.add_im, Complex.mul_im]
  rw [him]
  linarith [mul_le_mul_of_nonneg_left ((abs_add_le s.im T).trans (add_le_add hs (le_refl |T|))) hK,
    mul_le_mul_of_nonneg_right hKK' (abs_nonneg T)]

/-- A common exponential rate on the two ordinary halves and the existence of strip-growing
entire continuations on an initial disk imply an entire continuation of strip growth at one. -/
def CompactParameterStripGrowthStatement : Prop :=
  ∀ (F G : ℂ × ℂ → ℂ) (σ τ K : ℝ), 0 ≤ K →
    DifferentiableOn ℂ F (ball (0 : ℂ) 3 ×ˢ {s : ℂ | σ < s.re}) →
    DifferentiableOn ℂ G (ball (0 : ℂ) 3 ×ˢ {s : ℂ | s.re < τ}) →
    (∀ a b : ℝ, σ < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) 3,
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F (z, s)‖ ≤ C * Real.exp (K * |s.im|)) →
    (∀ a b : ℝ, b < τ → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) 3,
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G (z, s)‖ ≤ C * Real.exp (K * |s.im|)) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ∃ N : ℂ → ℂ, Differentiable ℂ N ∧
      HasStripExponentialGrowth N ∧ EqOn N (fun s => F (z, s)) {s : ℂ | σ < s.re} ∧
      EqOn N (fun s => G (z, s)) {s : ℂ | s.re < τ}) →
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧ HasStripExponentialGrowth N ∧
      EqOn N (fun s => F (1, s)) {s : ℂ | σ < s.re} ∧
      EqOn N (fun s => G (1, s)) {s : ℂ | s.re < τ}

set_option maxHeartbeats 1000000 in
theorem compactParameterStripGrowth : CompactParameterStripGrowthStatement := by
  intro F G σ τ K hK hF hG hRight hLeft ⟨δ, hδ, hInit⟩
  obtain ⟨N, hN, hNp, hNm⟩ := compactParameterEntireContinuation F G σ τ hF hG
    ⟨δ, hδ, fun z hz => by
      obtain ⟨Nz, hNz, _, hZp, hZm⟩ := hInit z hz
      exact ⟨Nz, hNz, hZp, hZm⟩⟩
  let K' := 1 + K ^ 2 / 4
  have hKK' : K ≤ K' := by dsimp only [K']; nlinarith [sq_nonneg (K - 2)]
  have hK' : 0 ≤ K' := hK.trans hKK'
  let P := ball (0 : ℂ) 3
  let U := {s : ℂ | σ < s.re}
  let s₀ : ℂ := ((σ + 2 : ℝ) : ℂ)
  let sh (T : ℝ) : ℂ := (T : ℂ) * Complex.I
  let weight (T : ℝ) : ℂ := (Real.exp (-K' * |T|) : ℂ)
  let Fw (T : ℝ) (p : ℂ × ℂ) := weight T * F (p.1, p.2 + sh T)
  let c (T : ℝ) (n : ℕ) (z : ℂ) := taylorCoeff (Fw T) s₀ 1 n z
  have hsh (T : ℝ) : (sh T).re = 0 := by simp [sh, Complex.mul_re]
  have hSph (R : ℝ) (w : ℂ) (hw : w ∈ sphere s₀ R) :
      σ + 2 - R ≤ w.re ∧ w.re ≤ σ + 2 + R ∧ |w.im| ≤ R := by
    have h : ‖w - s₀‖ = R := mem_sphere_iff_norm.mp hw
    have h₁ := (Complex.abs_re_le_norm (w - s₀)).trans_eq h
    have h₂ := (Complex.abs_im_le_norm (w - s₀)).trans_eq h
    simp only [Complex.sub_re, s₀, Complex.ofReal_re] at h₁
    simp only [Complex.sub_im, s₀, Complex.ofReal_im, sub_zero] at h₂
    exact ⟨by linarith [(abs_le.mp h₁).1], by linarith [(abs_le.mp h₁).2], h₂⟩
  have hFw (T : ℝ) : DifferentiableOn ℂ (Fw T) (P ×ˢ U) := by
    let L (x : ℂ × ℂ) := (x.1, x.2 + sh T)
    have hL : Differentiable ℂ L := differentiable_fst.prodMk (differentiable_snd.add_const _)
    have hmaps : MapsTo L (P ×ˢ U) (P ×ˢ U) := by
      intro p hp
      exact ⟨hp.1, by simpa [L, U, Complex.add_re, hsh] using hp.2⟩
    exact ((hF.comp hL.differentiableOn hmaps).const_mul _)
  have hUv : ball s₀ 2 ⊆ U := halfPlane_ball_subset σ
  have hFwz (T : ℝ) (s : ℂ) (hs : s ∈ U) : DifferentiableOn ℂ (fun z => Fw T (z, s)) P :=
    (hFw T).comp (Differentiable.prodMk differentiable_id (differentiable_const s)).differentiableOn
      (fun _ hz => ⟨hz, hs⟩)
  have hFws (T : ℝ) (z : ℂ) (hz : z ∈ P) :
      DifferentiableOn ℂ (fun s => Fw T (z, s)) (ball s₀ 2) :=
    (hFw T).comp (Differentiable.prodMk (differentiable_const z) differentiable_id).differentiableOn
      (fun _ hs => ⟨hz, hUv hs⟩)
  have hc (T : ℝ) (n : ℕ) : DifferentiableOn ℂ (c T n) P :=
    differentiableOn_taylorCoeff isOpen_ball (f := Fw T) (w₁ := s₀) one_pos
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2)
      (fun s hs => hFwz T s (hUv hs)) ((hFw T).continuousOn.mono (prod_mono subset_rfl hUv)) n
  obtain ⟨C₀, hC₀, hC₀'⟩ := hRight (σ + 1) (σ + 3) (by linarith)
  let A := C₀ * Real.exp K
  have hA₀ : 0 ≤ A := by dsimp [A]; positivity
  have hA (T : ℝ) (n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 2) : ‖c T n z‖ ≤ A := by
    have hBall := closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hz
    apply (norm_taylorCoeff_le (f := Fw T) (w₁ := s₀) one_pos (z := z) (M := A) ?_ n).trans_eq
      (by rw [one_pow, div_one])
    intro w hw
    obtain ⟨hw₁, hw₂, hw₃⟩ := hSph 1 w hw
    have he := hC₀' z hBall (w + sh T) (by rw [Complex.add_re, hsh, add_zero]; linarith)
      (by rw [Complex.add_re, hsh, add_zero]; linarith)
    simpa only [Fw, weight, A, mul_one] using norm_weighted_translate_le hC₀ hK hKK' hw₃ he
  let δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hInitStrip (a b : ℝ) (hab : a ≤ b) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ ball (0 : ℂ) δ', ∀ Z : ℂ → ℂ, Differentiable ℂ Z →
        HasStripExponentialGrowth Z → EqOn Z (fun s => F (z, s)) U →
        EqOn Z (fun s => G (z, s)) {s : ℂ | s.re < τ} →
        ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Z s‖ ≤ D * Real.exp (K' * |s.im|) := by
    let A₁ := min (a - 1) (τ - 1)
    let B₁ := max (b + 1) (σ + 1)
    have hAa : A₁ < a := (min_le_left _ _).trans_lt (by linarith)
    have hAt : A₁ < τ := (min_le_right _ _).trans_lt (by linarith)
    have hBb : b < B₁ := (by linarith : b < b + 1).trans_le (le_max_left _ _)
    have hBs : σ < B₁ := (by linarith : σ < σ + 1).trans_le (le_max_right _ _)
    obtain ⟨D₁, hD₁, hD₁'⟩ := hLeft A₁ A₁ hAt
    obtain ⟨D₂, hD₂, hD₂'⟩ := hRight B₁ B₁ hBs
    let D := max D₁ D₂
    have hD : 0 ≤ D := hD₁.trans (le_max_left _ _)
    let E : ℝ := (max |A₁| |B₁|) ^ 2 + K ^ 2 / 4
    refine ⟨D * Real.exp E, by positivity, fun z hz Z hZd hZG hZp hZm s ha hb => ?_⟩
    have hzP : z ∈ P := ball_subset_ball ((min_le_right _ _).trans (by norm_num)) hz
    have hline (w : ℂ) (hw : w.re = A₁ ∨ w.re = B₁) : ‖Z w‖ ≤ D * Real.exp (K * |w.im|) := by
      rcases hw with hw | hw
      · rw [hZm (show w.re < τ by rw [hw]; exact hAt)]
        exact (hD₁' z hzP w hw.ge hw.le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · rw [hZp (show σ < w.re by rw [hw]; exact hBs)]
        exact (hD₂' z hzP w hw.ge hw.le).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    rw [mul_assoc, ← Real.exp_add]
    exact norm_le_of_exp_bounds_on_vertical_lines hZd hZG (hAa.trans_le (hab.trans hBb.le)) hD hline
      (hAa.le.trans ha) (hb.trans hBb.le)
  have hDecay : ∀ b > (0 : ℝ), ∀ᶠ n in atTop, ∀ T z,
      z ∈ closedBall (0 : ℂ) (3 / 2) → ‖c T n z‖ ≤ b ^ n := by
    apply coefficientDecay_uniform c hc ⟨A, hA⟩
    refine ⟨δ', hδ', fun z hz b hb => ?_⟩
    obtain ⟨Z, hZd, hZG, hZp, hZm⟩ := hInit z (ball_subset_ball (min_le_left _ _) hz)
    have hzP : z ∈ P := ball_subset_ball ((min_le_right _ _).trans (by norm_num)) hz
    let R := 2 / b
    have hR : 0 < R := by positivity
    obtain ⟨D, hD, hD'⟩ := hInitStrip (σ + 2 - R) (σ + 2 + R) (by linarith)
    let D' := D * Real.exp (K' * R)
    have hpow : ∀ᶠ n : ℕ in atTop, D' ≤ (2 : ℝ) ^ n :=
      (tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))) D'
    filter_upwards [hpow] with n hn T
    let Zw (p : ℂ × ℂ) := weight T * Z (p.2 + sh T)
    have hZw : Differentiable ℂ (fun s => Zw (z, s)) := (hZd.comp (differentiable_id.add_const _)).const_mul _
    have he : (fun s => Fw T (z, s)) =ᶠ[𝓝 s₀] (fun s => Zw (z, s)) := by
      filter_upwards [ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 2)] with s hs
      have hh : σ < (s + sh T).re := by
        rw [Complex.add_re, hsh, add_zero]
        exact hUv hs
      exact congrArg (weight T * ·) (hZp hh).symm
    have hCoeff : c T n z = taylorCoeff Zw s₀ R n z := by
      dsimp only [c]
      rw [taylorCoeff_eq one_pos (by norm_num : (1 : ℝ) < 2) (hFws T z hzP),
        taylorCoeff_eq hR (lt_add_one R) hZw.differentiableOn, he.iteratedDeriv_eq n]
    rw [hCoeff]
    apply (norm_taylorCoeff_le hR (f := Zw) (M := D') ?_ n).trans
    · apply (div_le_iff₀ (pow_pos hR _)).mpr
      rw [← mul_pow, show b * R = 2 by dsimp [R]; field_simp]
      exact hn
    · intro w hw
      obtain ⟨hw₁, hw₂, hw₃⟩ := hSph R w hw
      have hbnd := hD' z hz Z hZd hZG hZp hZm (w + sh T)
        (by rw [Complex.add_re, hsh, add_zero]; exact hw₁)
        (by rw [Complex.add_re, hsh, add_zero]; exact hw₂)
      exact norm_weighted_translate_le hD hK' le_rfl hw₃ hbnd
  refine ⟨N, hN, ?_, hNp, hNm⟩
  intro a b
  let R := max |a - (σ + 2)| |b - (σ + 2)| + 1
  have hR : 0 < R := (abs_nonneg _).trans_lt (lt_add_of_le_of_pos (le_max_left _ _) one_pos)
  let ρ := (1 / 2 : ℝ) / R
  have hρ : 0 < ρ := div_pos (by norm_num) hR
  have h₁ : (1 : ℂ) ∈ closedBall (0 : ℂ) (3 / 2) := mem_closedBall_zero_iff.mpr (by norm_num)
  have h₁' : (1 : ℂ) ∈ P := closedBall_subset_ball (by norm_num) h₁
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hDecay ρ hρ)
  let u (j : ℕ) := if J ≤ j then (1 / 2 : ℝ) ^ j else A * R ^ j
  have hu : Summable u := by
    apply (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop J] with j hj
    simp [u, hj]
  have hu₀ (j : ℕ) : 0 ≤ u j := by
    by_cases hj : J ≤ j <;> simp [u, hj, mul_nonneg hA₀ (pow_nonneg hR.le _)]
  refine ⟨∑' j, u j, K', 0, tsum_nonneg hu₀, hK', fun s ha hb _ => ?_⟩
  let T := s.im
  let w : ℂ := s.re
  have hsw : w + sh T = s := by
    apply Complex.ext <;> simp [w, sh, T]
  have hw : ‖w - s₀‖ ≤ R := by
    rw [show w - s₀ = ((s.re - (σ + 2) : ℝ) : ℂ) by simp [w, s₀], Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    have ha' := le_max_left |a - (σ + 2)| |b - (σ + 2)|
    have hb' := le_max_right |a - (σ + 2)| |b - (σ + 2)|
    dsimp only [R]
    constructor <;> linarith [neg_abs_le (a - (σ + 2)), le_abs_self (b - (σ + 2))]
  let Nw (p : ℂ × ℂ) := weight T * N (p.2 + sh T)
  have hNw : Differentiable ℂ (fun s => Nw (1, s)) := (hN.comp (differentiable_id.add_const _)).const_mul _
  have he : (fun s => Fw T (1, s)) =ᶠ[𝓝 s₀] (fun s => Nw (1, s)) := by
    filter_upwards [ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 2)] with s hs
    have hh : σ < (s + sh T).re := by rw [Complex.add_re, hsh, add_zero]; exact hUv hs
    exact congrArg (weight T * ·) (hNp hh).symm
  have hcoeff (j : ℕ) : c T j 1 = taylorCoeff Nw s₀ 1 j 1 := by
    dsimp only [c]
    rw [taylorCoeff_eq one_pos (by norm_num : (1 : ℝ) < 2) (hFws T 1 h₁'),
      taylorCoeff_eq one_pos (by norm_num : (1 : ℝ) < 2) hNw.differentiableOn, he.iteratedDeriv_eq j]
  have hseries := hasSum_taylorCoeff (f := Nw) (z := 1) (w₁ := s₀) (R := R + 2) one_pos
    (by linarith) hNw.differentiableOn
    (mem_ball_iff_norm.mpr (hw.trans_lt (lt_add_of_pos_right R (by norm_num : (0 : ℝ) < 2))))
  have hTerm (j : ℕ) : ‖c T j 1 * (w - s₀) ^ j‖ ≤ u j := by
    rw [norm_mul, norm_pow]
    by_cases hj : J ≤ j
    · simp only [u, ite_eq_left hj]
      calc
        _ ≤ ρ ^ j * R ^ j := mul_le_mul (hJ j hj T 1 h₁)
          (pow_le_pow_left₀ (norm_nonneg _) hw _) (by positivity) (by positivity)
        _ = _ := by rw [← mul_pow]; dsimp only [ρ]; rw [div_mul_cancel₀ _ hR.ne']
    · simp only [u, ite_eq_right hj]
      exact mul_le_mul (hA T j 1 (closedBall_subset_closedBall (by norm_num) h₁))
        (pow_le_pow_left₀ (norm_nonneg _) hw _)
        (by positivity) hA₀
  simp_rw [← hcoeff] at hseries
  have hsum := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hTerm hu
  have hNorm : ‖weight T * N s‖ ≤ ∑' j, u j := by
    rw [← hsw]
    change ‖Nw (1, w)‖ ≤ _
    rw [← hseries.tsum_eq]
    exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hTerm hu)
  dsimp only [weight] at hNorm
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le] at hNorm
  rw [mul_comm] at hNorm
  have hh := (le_div_iff₀ (Real.exp_pos (-K' * |T|))).mpr hNorm
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul, neg_neg, T] using hh

end Langlands.Analysis.SeveralComplex
