import Langlands.Analysis.TestedExponentialSector

/-! # Exponential decay with a regularity condition on truncation parameters -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Topology

set_option autoImplicit false

namespace Langlands.Analysis

/-- A sector increment estimate may be available only for regular starting points, for example
those above a fixed threshold in every simple root. The regular points contain the sector
outside a large ball and stay regular under enlargement along their own rays. Vanishing
smooth tests at infinity then give the exponential bound at every regular point of norm at
least one, with the same geometric-series constant as for a radial threshold. -/
def TestedRegularSectorStatement : Prop :=
  ∀ {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] (C : Set V) (regular : V → Prop) (U : Set X) (f : V → X → ℂ),
    let l := comap (fun t : V => ‖t‖) atTop ⊓ 𝓟 C
    let Increments (A : Set X) (B ε : ℝ) :=
      ∀ x ∈ A, ∀ t ∈ C, ∀ s ∈ C, regular t → 1 ≤ ‖t‖ → ‖s‖ ≤ ‖t‖ →
        dist (f t x) (f (t + s) x) ≤ B * Real.exp (-ε * ‖t‖)
    (∃ u ∈ C, ‖u‖ = 1) →
    (∀ t ∈ C, ∀ r : ℝ, 0 < r → r • t ∈ C) →
    (∀ t ∈ C, regular t → ∀ r : ℝ, 1 ≤ r → regular (r • t)) →
    (∃ R : ℝ, ∀ t ∈ C, R ≤ ‖t‖ → regular t) → IsOpen U →
    (∀ᶠ t in l, ContinuousOn (f t) U) →
    (∀ A ⊆ U, IsCompact A → ∃ B ε : ℝ, 0 ≤ B ∧ 0 < ε ∧ Increments A B ε) →
    (∀ β : X → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      Tendsto (fun t => ∫ x, β x • f t x ∂μ) l (𝓝 0)) →
    ∀ A ⊆ U, ∀ B ε : ℝ, 0 ≤ B → 0 < ε → Increments A B ε →
      ∀ x ∈ A, ∀ t ∈ C, regular t → 1 ≤ ‖t‖ →
        ‖f t x‖ ≤ B * Real.exp (-ε * ‖t‖) / (1 - Real.exp (-ε))

/-- First apply the sector theorem beyond the radial threshold. Then follow the ray from each
regular point, using unit increments with an exponentially summable bound. -/
theorem testedRegularSector : TestedRegularSectorStatement := by
  intro V X _ _ _ _ _ _ _ μ _ _ C regular U f l Increments hunit hscale hregScale hfar hU
    hcont hinc htest A hA B ε hB hε hstep x hx t ht hreg ht1
  obtain ⟨R, hR⟩ := hfar
  let R' := max R 1
  have htail (r : V) (hr : r ∈ C) (hrn : R' ≤ ‖r‖) :
      ‖f r x‖ ≤ B * Real.exp (-ε * ‖r‖) / (1 - Real.exp (-ε)) :=
    testedExponentialSector μ C U f R' (le_max_right _ _) hunit hscale hU hcont
      (fun S hSU hSc => by
        obtain ⟨D, η, hD, hη, hS⟩ := hinc S hSU hSc
        exact ⟨D, η, hD, hη, fun y hy r hr s hs hrn hsr =>
          hS y hy r hr s hs (hR r hr ((le_max_left _ _).trans hrn))
            ((le_max_right _ _).trans hrn) hsr⟩)
      htest A hA B ε hB hε
      (fun y hy r hr s hs hrn hsr => hstep y hy r hr s hs
        (hR r hr ((le_max_left _ _).trans hrn)) ((le_max_right _ _).trans hrn) hsr)
      x hx r hr hrn
  have htn : 0 < ‖t‖ := zero_lt_one.trans_le ht1
  let u := ‖t‖⁻¹ • t
  have hu : u ∈ C := hscale t ht _ (inv_pos.mpr htn)
  have hun : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htn.le), inv_mul_cancel₀ htn.ne']
  have ht_eq : ‖t‖ • u = t := by rw [smul_smul, mul_inv_cancel₀ htn.ne', one_smul]
  let r (j : ℕ) : V := (‖t‖ + (j : ℝ)) • u
  have hpos (j : ℕ) : 0 < ‖t‖ + (j : ℝ) := by positivity
  have hr_mem (j : ℕ) : r j ∈ C := hscale u hu _ (hpos j)
  have hr_norm (j : ℕ) : ‖r j‖ = ‖t‖ + (j : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (hpos j).le, hun, mul_one]
  have hr_reg (j : ℕ) : regular (r j) := by
    have hc : 1 ≤ (‖t‖ + (j : ℝ)) * ‖t‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ htn, one_mul]
      exact le_add_of_nonneg_right (Nat.cast_nonneg j)
    have h := hregScale t ht hreg _ hc
    simpa only [r, u, smul_smul] using h
  let q := Real.exp (-ε)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε)
  have hgeometric (j : ℕ) :
      dist (f (r j) x) (f (r (j + 1)) x) ≤ (B * Real.exp (-ε * ‖t‖)) * q ^ j := by
    have hr1 : 1 ≤ ‖r j‖ := by rw [hr_norm]; exact ht1.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
    have hs := hstep x hx (r j) (hr_mem j) u hu (hr_reg j) hr1 (hun.symm ▸ hr1)
    have hnext : r j + u = r (j + 1) := by
      change (‖t‖ + (j : ℝ)) • u + u = (‖t‖ + ((j + 1 : ℕ) : ℝ)) • u
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc, add_smul, one_smul]
    rw [hnext, hr_norm] at hs
    calc
      _ ≤ B * Real.exp (-ε * (‖t‖ + (j : ℝ))) := hs
      _ = _ := by rw [mul_add, Real.exp_add, mul_comm (-ε) (j : ℝ), Real.exp_nat_mul, mul_assoc]
  have hnorm : Tendsto (fun j => ‖r j‖) atTop atTop := by
    simpa only [hr_norm] using
      tendsto_atTop_add_const_left atTop ‖t‖ (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun j => f (r j) x) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hnorm.eventually_ge_atTop R'] with j hj
      exact htail (r j) (hr_mem j) hj
    · have h := Real.tendsto_exp_atBot.comp (hnorm.const_mul_atTop_of_neg (neg_neg_of_pos hε))
      simpa only [Function.comp_apply, mul_zero, zero_div] using
        ((h.const_mul B).div_const (1 - q))
  have hfirst : r 0 = t := by simpa only [r, Nat.cast_zero, add_zero] using ht_eq
  simpa only [hfirst, dist_zero_right] using
    dist_le_of_le_geometric_of_tendsto₀ q _ hq hgeometric hlim

end Langlands.Analysis
