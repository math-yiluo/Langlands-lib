import Langlands.Analysis.SeveralComplex.Hartogs.HartogsLemma
import Mathlib.Analysis.Complex.AbsMax

/-! # Propagation of geometric bounds for holomorphic Taylor coefficients -/

noncomputable section

open Metric Set Filter
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SeveralComplex

private theorem eventually_norm_le_pow_of_pointwise {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {g : ℕ → ℂ → ℂ}
    (hg : ∀ n, DifferentiableOn ℂ (g n) U) {A : ℝ} (hb : ∀ n z, z ∈ U → ‖g n z‖ ≤ A)
    (hp : ∀ z ∈ U, ∀ b : ℝ, 0 < b → ∀ᶠ n in atTop, ‖g n z‖ ≤ b ^ n)
    {b : ℝ} (hb₀ : 0 < b) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ‖g n z‖ ≤ b ^ n := by
  let c := b / Real.exp 2
  have hc : 0 < c := div_pos hb₀ (Real.exp_pos _)
  let G (n : ℕ) (z : ℂ) := ((c⁻¹ : ℝ) : ℂ) ^ n * g n z
  have hN (n : ℕ) (z : ℂ) : ‖G n z‖ = (c⁻¹) ^ n * ‖g n z‖ := by
    dsimp only [G]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hc).le]
  have hh (z : K) : ∃ r > 0, ∀ᶠ n in atTop, ∀ w ∈ ball z.val r, ‖g n w‖ ≤ b ^ n := by
    obtain ⟨r, hr, h⟩ := exists_ball_eventually_norm_le_exp hU
      (fun n => (hg n).const_mul _) (A := A) (T := c⁻¹) (g := G)
      (fun n w hw => by rw [hN, mul_comm A]; exact mul_le_mul_of_nonneg_left (hb n w hw) (by positivity))
      (fun w hw => (hp w hw c hc).mono fun n hn => by
        rw [hN]
        calc
          _ ≤ (c⁻¹) ^ n * c ^ n := mul_le_mul_of_nonneg_left hn (by positivity)
          _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow])
      (hKU z.2) (ε := 1) one_pos
    refine ⟨r, hr, ?_⟩
    filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn₁ w hw
    have hExp : Real.exp (((n : ℝ) + 1) * 1) ≤ Real.exp 2 ^ n := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
      linarith
    calc
      ‖g n w‖ = c ^ n * ‖G n w‖ := by rw [hN, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_mul]
      _ ≤ c ^ n * Real.exp 2 ^ n :=
        mul_le_mul_of_nonneg_left ((hn w hw).trans hExp) (by positivity)
      _ = b ^ n := by
        rw [← mul_pow]
        dsimp only [c]
        rw [div_mul_cancel₀ _ (Real.exp_ne_zero _)]
  choose R hR h using hh
  obtain ⟨I, hCover⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (R x)) (fun _ => isOpen_ball) <|
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hR ⟨x, hx⟩)⟩
  have hI : ∀ᶠ n in atTop, ∀ i ∈ I, ∀ w ∈ ball i.val (R i), ‖g n w‖ ≤ b ^ n :=
    (eventually_all_finset I).2 fun i _ => h i
  filter_upwards [hI] with n hn z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hz)
  obtain ⟨hiI, hzi⟩ := mem_iUnion.mp hi
  exact hn i hiI z hzi

private theorem pow_scaled_annulus_bound {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 3))
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} {C : ℝ}
    (hOuter : ∀ z : ℂ, ‖z‖ = 2 → ‖g z‖ / 2 ^ n ≤ C)
    (hInner : ∀ z : ℂ, ‖z‖ = ρ → ‖g z‖ / ρ ^ n ≤ C)
    {z : ℂ} (hz₁ : ρ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ 2) :
    ‖g z‖ / ‖z‖ ^ n ≤ C := by
  let U : Set ℂ := {z | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ 2}
  have hUc : IsClosed U :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hUb : Bornology.IsBounded U := isBounded_closedBall.subset fun _ hz =>
    mem_closedBall_zero_iff.mpr hz.2
  have hFront (w : ℂ) (hw : w ∈ frontier U) : ‖w‖ = 2 ∨ ‖w‖ = ρ := by
    have hwU : w ∈ U := hUc.closure_eq ▸ frontier_subset_closure hw
    rcases eq_or_lt_of_le hwU.2 with h | h
    · exact Or.inl h
    rcases eq_or_lt_of_le hwU.1 with h' | h'
    · exact Or.inr h'.symm
    let V : Set ℂ := {w | ρ < ‖w‖ ∧ ‖w‖ < 2}
    have hVo : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
    have hVU : V ⊆ U := fun _ hw => ⟨hw.1.le, hw.2.le⟩
    exact (hw.2 (interior_maximal hVU hVo ⟨h', h⟩)).elim
  let f (w : ℂ) := g w / w ^ n
  have hf : DifferentiableOn ℂ f U := by
    apply (hg.mono fun _ hw => mem_ball_zero_iff.mpr (hw.2.trans_lt (by norm_num))).div
      (differentiableOn_id.pow _)
    intro w hw
    exact pow_ne_zero _ (norm_pos_iff.mp (hρ.trans_le hw.1))
  have hf' : DiffContOnCl ℂ f U := ⟨hf, hUc.closure_eq.symm ▸ hf.continuousOn⟩
  have hC (w : ℂ) (hw : w ∈ frontier U) : ‖f w‖ ≤ C := by
    rcases hFront w hw with h | h
    · simpa only [f, norm_div, norm_pow, h] using hOuter w h
    · simpa only [f, norm_div, norm_pow, h] using hInner w h
  simpa only [f, norm_div, norm_pow] using
    Complex.norm_le_of_forall_mem_frontier_norm_le hUb hf' hC (subset_closure ⟨hz₁, hz₂⟩)

/-- Geometric decay at every rate on a small open parameter disk propagates
to uniform decay at every rate on a larger compact disk. -/
def HolomorphicCoefficientDecayStatement : Prop :=
  ∀ (g : ℕ → ℂ → ℂ), (∀ n, DifferentiableOn ℂ (g n) (ball 0 3)) →
    (∃ A : ℝ, ∀ n z, z ∈ closedBall 0 2 → ‖g n z‖ ≤ A) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, ∀ b : ℝ, 0 < b → ∀ᶠ n in atTop, ‖g n z‖ ≤ b ^ n) →
    ∀ b : ℝ, 0 < b → ∀ᶠ n in atTop, ∀ z ∈ closedBall 0 (3 / 2), ‖g n z‖ ≤ b ^ n

theorem holomorphicCoefficientDecay : HolomorphicCoefficientDecayStatement := by
  intro g hg ⟨A, hA⟩ ⟨δ, hδ, hpoint⟩ b hb
  let R : ℝ := 3 / 2
  let u : ℝ := min δ 1
  let ρ : ℝ := u / 2
  have hu : 0 < u := lt_min hδ one_pos
  have hρ : 0 < ρ := by positivity
  have hρu : ρ < u := by dsimp only [ρ]; linarith
  have hUniform (c : ℝ) (hc : 0 < c) :
      ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) ρ, ‖g n z‖ ≤ c ^ n := by
    apply eventually_norm_le_pow_of_pointwise (U := ball 0 u) isOpen_ball (isCompact_closedBall _ _)
      (closedBall_subset_ball hρu) (A := A) ?_ ?_ ?_ hc
    · exact fun n => (hg n).mono (ball_subset_ball ((min_le_right δ 1).trans (by norm_num)))
    · exact fun n z hz => hA n z ((ball_subset_closedBall.trans
        (closedBall_subset_closedBall ((min_le_right δ 1).trans (by norm_num)))) hz)
    · exact fun z hz => hpoint z (ball_subset_ball (min_le_left _ _) hz)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hb (show R / 2 < 1 by norm_num [R])
  let c := b / R ^ k
  have hR : 0 < R := by norm_num [R]
  have hc : 0 < c := div_pos hb (by positivity)
  have hbase : 1 < c * 2 ^ k := by
    have hk' : R ^ k / 2 ^ k < b := by simpa only [div_pow] using hk
    have h := (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mp hk'
    dsimp only [c]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    simpa only [one_mul] using h
  have hOut : ∀ᶠ n : ℕ in atTop, A ≤ (c * 2 ^ k) ^ n :=
    (tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt hbase)) A
  filter_upwards [hUniform (min b (c * ρ ^ k)) (lt_min hb (by positivity)), hOut] with n hn hOutn z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  rcases le_or_gt ‖z‖ ρ with hzρ | hzρ
  · exact (hn z (mem_closedBall_zero_iff.mpr hzρ)).trans
      (pow_le_pow_left₀ (le_of_lt (lt_min hb (by positivity))) (min_le_left _ _) _)
  have hNorm := pow_scaled_annulus_bound (hg n) hρ (n := k * n) (C := c ^ n)
    (fun w hw => by
      apply (div_le_iff₀ (by positivity)).mpr
      calc
        ‖g n w‖ ≤ A := hA n w (mem_closedBall_zero_iff.mpr hw.le)
        _ ≤ (c * 2 ^ k) ^ n := hOutn
        _ = c ^ n * 2 ^ (k * n) := by rw [mul_pow, pow_mul])
    (fun w hw => by
      apply (div_le_iff₀ (by positivity)).mpr
      calc
        ‖g n w‖ ≤ min b (c * ρ ^ k) ^ n := hn w (mem_closedBall_zero_iff.mpr hw.le)
        _ ≤ (c * ρ ^ k) ^ n :=
          pow_le_pow_left₀ (le_of_lt (lt_min hb (by positivity))) (min_le_right _ _) _
        _ = c ^ n * ρ ^ (k * n) := by rw [mul_pow, pow_mul])
    hzρ.le (hzR.trans (by norm_num [R]))
  have hzpos : 0 < ‖z‖ := hρ.trans hzρ
  calc
    ‖g n z‖ ≤ c ^ n * ‖z‖ ^ (k * n) := (div_le_iff₀ (by positivity)).mp hNorm
    _ ≤ c ^ n * R ^ (k * n) := by gcongr
    _ = b ^ n := by
      rw [pow_mul, ← mul_pow]
      dsimp only [c]
      rw [div_mul_cancel₀ _ (by positivity)]

end Langlands.Analysis.SeveralComplex
