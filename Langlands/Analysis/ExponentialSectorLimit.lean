import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.Basic

/-! # Exponential limits from increment estimates on a sector -/

noncomputable section

open Filter Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

private theorem tendsto_exp_neg_mul {A : Type*} {l : Filter A} {r : A → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hr : Tendsto r l atTop) :
    Tendsto (fun t => Real.exp (-ε * r t)) l (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (hr.const_mul_atTop_of_neg (neg_neg_of_pos hε))

/-- An exponential bound for positive comparable increments gives a common limit on a sector
with the same exponential rate. The sector is closed under positive real scaling and contains
a unit vector. -/
def ExponentialSectorLimitStatement : Prop :=
  ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace W] [CompleteSpace W] (C : Set V) (f : V → W) (R B ε : ℝ),
    1 ≤ R → 0 ≤ B → 0 < ε →
    (∃ u ∈ C, ‖u‖ = 1) →
    (∀ u ∈ C, ∀ r : ℝ, 0 < r → r • u ∈ C) →
    (∀ x ∈ C, ∀ y ∈ C, R ≤ ‖x‖ → ‖y‖ ≤ ‖x‖ →
      dist (f x) (f (x + y)) ≤ B * Real.exp (-ε * ‖x‖)) →
    ∃ L : W, Tendsto f (comap (fun x : V => ‖x‖) atTop ⊓ 𝓟 C) (𝓝 L) ∧
      ∀ x ∈ C, R ≤ ‖x‖ →
        dist (f x) L ≤ B * Real.exp (-ε * ‖x‖) / (1 - Real.exp (-ε))

theorem exponentialSectorLimit : ExponentialSectorLimitStatement := by
  intro V W _ _ _ _ C f R B ε hR hB hε hbase hC hinc
  obtain ⟨u, hu, hun⟩ := hbase
  let g (v : V) (r : ℝ) : W := f (r • v)
  let q := Real.exp (-ε)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hrayNorm (v : V) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r) : ‖r • v‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, hv, mul_one]
  have hstep (v : V) (hv : v ∈ C) (hvn : ‖v‖ = 1) {r s : ℝ}
      (hr : R ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) :
      dist (g v r) (g v (r + s)) ≤ B * Real.exp (-ε * r) := by
    rcases hs.eq_or_lt with hzero | hs
    · subst s
      simpa only [add_zero, dist_self] using mul_nonneg hB (Real.exp_pos _).le
    have hr0 := hRpos.trans_le hr
    have h := hinc (r • v) (hC v hv r hr0) (s • v) (hC v hv s hs)
    rw [hrayNorm _ hvn hr0.le, hrayNorm _ hvn hs.le] at h
    simpa only [g, add_smul] using h hr hsr
  have hcompare (v : V) (hv : v ∈ C) (hvn : ‖v‖ = 1) {r : ℝ} (hr : R ≤ r) :
      dist (g u r) (g v r) ≤ 2 * B * Real.exp (-ε * r) := by
    have hr0 := hRpos.trans_le hr
    have hu' := hC u hu r hr0
    have hv' := hC v hv r hr0
    have h₁ := hinc _ hu' _ hv'
    have h₂ := hinc _ hv' _ hu'
    rw [hrayNorm _ hun hr0.le, hrayNorm _ hvn hr0.le] at h₁ h₂
    have h₂' : dist (f (r • u + r • v)) (g v r) ≤ B * Real.exp (-ε * r) := by
      rw [dist_comm, add_comm (r • u) (r • v)]
      exact h₂ hr le_rfl
    calc
      _ ≤ dist (g u r) (f (r • u + r • v)) + dist (f (r • u + r • v)) (g v r) :=
        dist_triangle _ _ _
      _ ≤ _ := by linarith [h₁ hr le_rfl]
  have hgeometric (v : V) (hv : v ∈ C) (hvn : ‖v‖ = 1) {r : ℝ} (hr : R ≤ r) (n : ℕ) :
      dist (g v (r + n)) (g v (r + (n + 1 : ℕ))) ≤
        (B * Real.exp (-ε * r)) * q ^ n := by
    have hrn : R ≤ r + (n : ℝ) := hr.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
    have hs : 1 ≤ r + (n : ℝ) := hR.trans hrn
    have h := hstep v hv hvn hrn zero_le_one hs
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    calc
      _ ≤ B * Real.exp (-ε * (r + n)) := h
      _ = _ := by rw [mul_add, Real.exp_add, mul_comm (-ε) (n : ℝ), Real.exp_nat_mul, mul_assoc]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric q (B * Real.exp (-ε * R)) hq (hgeometric u hu hun le_rfl))
  have hlimit (v : V) (hv : v ∈ C) (hvn : ‖v‖ = 1) {r : ℝ} (hr : R ≤ r) :
      Tendsto (fun n : ℕ => g v (r + n)) atTop (𝓝 L) := by
    apply hL.congr_dist
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hRnInf : Tendsto (fun n : ℕ => R + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop R hnat
    have hdecay := (tendsto_exp_neg_mul hε hRnInf).const_mul (3 * B)
    simp only [mul_zero] at hdecay
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hdecay
    filter_upwards [hnat.eventually_ge_atTop (r - R)] with n hn
    have hRn : R ≤ R + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have h₁ := hcompare v hv hvn hRn
    have h₂ := hstep v hv hvn hRn (sub_nonneg.mpr hr) (hn.trans (le_add_of_nonneg_left hRpos.le))
    rw [show R + (n : ℝ) + (r - R) = r + n by ring] at h₂
    calc
      _ ≤ dist (g u (R + n)) (g v (R + n)) +
          dist (g v (R + n)) (g v (r + n)) := dist_triangle _ _ _
      _ ≤ _ := by linarith
  have hbound (x : V) (hx : x ∈ C) (hr : R ≤ ‖x‖) :
      dist (f x) L ≤ B * Real.exp (-ε * ‖x‖) / (1 - q) := by
    have hxpos := hRpos.trans_le hr
    let v := ‖x‖⁻¹ • x
    have hv := hC x hx _ (inv_pos.mpr hxpos)
    have hvn : ‖v‖ = 1 := by
      change ‖‖x‖⁻¹ • x‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
    have h := dist_le_of_le_geometric_of_tendsto₀ q _ hq (hgeometric v hv hvn hr)
      (hlimit v hv hvn hr)
    simpa only [Nat.cast_zero, add_zero, g, v, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul] using h
  refine ⟨L, tendsto_iff_dist_tendsto_zero.mpr ?_, hbound⟩
  have hscale : Tendsto (fun x : V => ‖x‖) (comap (fun x : V => ‖x‖) atTop ⊓ 𝓟 C) atTop :=
    (tendsto_comap : Tendsto (fun x : V => ‖x‖) _ atTop).mono_left inf_le_left
  have hmem : ∀ᶠ x in comap (fun x : V => ‖x‖) atTop ⊓ 𝓟 C, x ∈ C :=
    le_principal_iff.mp inf_le_right
  have hdecay : Tendsto (fun x : V => B * Real.exp (-ε * ‖x‖) / (1 - q))
      (comap (fun x : V => ‖x‖) atTop ⊓ 𝓟 C) (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      ((tendsto_exp_neg_mul hε hscale).const_mul B).div_const (1 - q)
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hdecay
  filter_upwards [hmem, hscale.eventually_ge_atTop R] with x hx hr
  exact hbound x hx hr

end Langlands.Analysis
