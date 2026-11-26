import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Analysis.AntiperiodicIntegralDecay
import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.AdelicEisensteinWeakConstantTermApproximationStatement
import Langlands.Global.AdelicEisensteinUniformTemperednessStatement
import Langlands.Global.AdelicSiegelChamberGeometryStatement
import Langlands.Global.AdelicEisensteinAmbientShiftProof
import Langlands.Global.AdelicEisensteinRegularParameterProof
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicEisensteinConjugateParabolicHeight

/-! # The chamber estimate for wave packets from the weak constant term

This module proves `WavePacketChamberDecayStatement` from three propositions:
`EisensteinWeakConstantTermApproximationStatement` (Delorme 2023, Lemma 5.3 with (4.3)),
`EisensteinUniformTemperednessStatement` (Delorme 2023, Proposition 4.1) and
`SiegelChamberGeometryStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Metric Set
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.ChamberDecay

/-! ### Elementary inequalities -/

/-- `(∑ a_i)^k ≤ (#s)^k ∑ a_i^k` for nonnegative `a_i` on a nonempty finite set. -/
theorem pow_sum_le_card_pow_mul_sum_pow {Ix : Type*} (s : Finset Ix) (hs : s.Nonempty)
    (f : Ix → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (k : ℕ) :
    (∑ i ∈ s, f i) ^ k ≤ (s.card : ℝ) ^ k * ∑ i ∈ s, f i ^ k := by
  have hc : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  rcases k with _ | k
  · simp only [pow_zero, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact hc
  · calc (∑ i ∈ s, f i) ^ (k + 1) ≤ (s.card : ℝ) ^ k * ∑ i ∈ s, f i ^ (k + 1) :=
          pow_sum_le_card_mul_sum_pow hf k
      _ ≤ (s.card : ℝ) ^ (k + 1) * ∑ i ∈ s, f i ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (Nat.le_succ k))
            (Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) _)

/-- **Combination of decay estimates.** If `Θ (1 + Y_i)^k ≤ C_{i,k} w s^m` for every index `i` of a
nonempty finite type and every `k`, and `s ≤ C ∑_i (1 + Y_i)` with `s ≥ 1`, then for every `n`,
`Θ s^n ≤ B w`. -/
theorem le_mul_of_decay {Ix X : Type*} [Fintype Ix] [Nonempty Ix] (Θ w s : X → ℝ) (Y : Ix → X → ℝ)
    (m : ℕ) (hΘ : ∀ g, 0 ≤ Θ g) (hw : ∀ g, 0 ≤ w g) (hs : ∀ g, 1 ≤ s g)
    (hY : ∀ i g, 0 ≤ Y i g)
    (hdec : ∀ i (k : ℕ), ∃ C : ℝ, ∀ g, Θ g * (1 + Y i g) ^ k ≤ C * (w g * s g ^ m))
    (hH : ∃ C : ℝ, ∀ g, s g ≤ C * ∑ i, (1 + Y i g)) (n : ℕ) :
    ∃ B : ℝ, ∀ g, Θ g * s g ^ n ≤ B * w g := by
  classical
  obtain ⟨CH, hCH⟩ := hH
  choose C hC using fun i => hdec i (m + n)
  set N : ℝ := ((Finset.univ : Finset Ix).card : ℝ)
  refine ⟨|CH| ^ (m + n) * N ^ (m + n) * ∑ i, |C i|, fun g => ?_⟩
  have hspos : 0 < s g := lt_of_lt_of_le one_pos (hs g)
  have hsum0 : ∀ i ∈ (Finset.univ : Finset Ix), 0 ≤ 1 + Y i g :=
    fun i _ => by linarith [hY i g]
  have hS : s g ≤ |CH| * ∑ i, (1 + Y i g) :=
    (hCH g).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Finset.sum_nonneg hsum0))
  have hpow : s g ^ (m + n) ≤ |CH| ^ (m + n) * (N ^ (m + n) * ∑ i, (1 + Y i g) ^ (m + n)) := by
    calc s g ^ (m + n) ≤ (|CH| * ∑ i, (1 + Y i g)) ^ (m + n) :=
          pow_le_pow_left₀ hspos.le hS _
      _ = |CH| ^ (m + n) * (∑ i, (1 + Y i g)) ^ (m + n) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_sum_le_card_pow_mul_sum_pow _ Finset.univ_nonempty _ hsum0 _)
          (pow_nonneg (abs_nonneg _) _)
  have hmain : Θ g * s g ^ (m + n) ≤
      (|CH| ^ (m + n) * N ^ (m + n) * ∑ i, |C i|) * (w g * s g ^ m) := by
    calc Θ g * s g ^ (m + n)
        ≤ Θ g * (|CH| ^ (m + n) * (N ^ (m + n) * ∑ i, (1 + Y i g) ^ (m + n))) :=
          mul_le_mul_of_nonneg_left hpow (hΘ g)
      _ = |CH| ^ (m + n) * N ^ (m + n) * ∑ i, Θ g * (1 + Y i g) ^ (m + n) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ |CH| ^ (m + n) * N ^ (m + n) * ∑ i, |C i| * (w g * s g ^ m) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
          exact (hC i g).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg (hw g) (pow_nonneg hspos.le _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hsm : 0 < s g ^ m := pow_pos hspos m
  rw [pow_add] at hmain
  have : Θ g * s g ^ n * s g ^ m ≤ (|CH| ^ (m + n) * N ^ (m + n) * ∑ i, |C i|) * w g * s g ^ m := by
    nlinarith [hmain]
  exact le_of_mul_le_mul_right this hsm

/-- Exponential decay beats every polynomial: `(1 + R)^k e^{-ε R}` is bounded on `R ≥ 0`. -/
theorem exists_one_add_pow_mul_exp_neg_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R → (1 + R) ^ k * Real.exp (-(ε * R)) ≤ C := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun R hR => ?_⟩
    simp only [pow_zero, one_mul, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  set a : ℝ := ε / k with ha
  have ha0 : 0 < a := div_pos hε (by exact_mod_cast hk)
  set b : ℝ := max 1 (1 / a)
  refine ⟨b ^ k, fun R hR => ?_⟩
  have h1 : 1 + R ≤ b * (1 + a * R) := by
    have hb1 : 1 ≤ b := le_max_left _ _
    have hb2 : 1 / a ≤ b := le_max_right _ _
    have : R ≤ b * (a * R) := by
      have := mul_le_mul_of_nonneg_right hb2 (mul_nonneg ha0.le hR)
      rwa [one_div, inv_mul_cancel_left₀ ha0.ne'] at this
    nlinarith
  have h2 : 1 + a * R ≤ Real.exp (a * R) := by
    have := Real.add_one_le_exp (a * R); linarith
  have h3 : (1 + R) ^ k ≤ b ^ k * Real.exp (ε * R) := by
    calc (1 + R) ^ k ≤ (b * (1 + a * R)) ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ = b ^ k * (1 + a * R) ^ k := mul_pow _ _ _
      _ ≤ b ^ k * Real.exp (a * R) ^ k := by
          gcongr
      _ = b ^ k * Real.exp (ε * R) := by
          rw [← Real.exp_nat_mul]
          congr 2
          rw [ha]
          field_simp
  calc (1 + R) ^ k * Real.exp (-(ε * R)) ≤ b ^ k * Real.exp (ε * R) * Real.exp (-(ε * R)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = b ^ k := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- `w s^m` is monotone in `m` when `w ≥ 0` and `s ≥ 1`. -/
theorem mul_pow_le_mul_pow {w s : ℝ} (hw : 0 ≤ w) (hs : 1 ≤ s) {m m' : ℕ} (hm : m ≤ m') :
    w * s ^ m ≤ w * s ^ m' :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs hm) hw

/-- **Uniformization over a finite set.** If for each `a ∈ S` there is an exponent `m_a` such that
for every `k` some constant `C ≥ 0` satisfies `Pr a m_a k C`, and `Pr` is monotone in the exponent
and in nonnegative constants, then one exponent and, for each `k`, one constant serve every
`a ∈ S`. -/
theorem exists_uniform {α : Type*} [DecidableEq α] (S : Finset α) (Pr : α → ℕ → ℕ → ℝ → Prop)
    (hmono : ∀ a m m' k C C', m ≤ m' → C ≤ C' → 0 ≤ C → Pr a m k C → Pr a m' k C')
    (h : ∀ a ∈ S, ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ Pr a m k C) :
    ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, Pr a m k C := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun _ => ⟨0, le_rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩⟩
  | insert a S haS ih =>
    obtain ⟨ma, hma⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨mS, hmS⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨max ma mS, fun k => ?_⟩
    obtain ⟨Ca, hCa0, hCa⟩ := hma k
    obtain ⟨CS, hCS0, hCS⟩ := hmS k
    refine ⟨max Ca CS, hCa0.trans (le_max_left _ _), fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hmono b ma _ k Ca _ (le_max_left _ _) (le_max_left _ _) hCa0 hCa
    · exact hmono b mS _ k CS _ (le_max_right _ _) (le_max_right _ _) hCS0 (hCS b hb)

/-- The monotonicity of bounds `Θ (1 + Y)^k ≤ C w s^m` used with `exists_uniform`. -/
theorem le_mul_mono {Θ Y w s C C' : ℝ} {k m m' : ℕ} (hw : 0 ≤ w) (hs : 1 ≤ s) (hmm : m ≤ m')
    (hCC : C ≤ C') (hC : 0 ≤ C) (h : Θ * (1 + Y) ^ k ≤ C * (w * s ^ m)) :
    Θ * (1 + Y) ^ k ≤ C' * (w * s ^ m') :=
  h.trans (mul_le_mul hCC (mul_pow_le_mul_pow hw hs hmm)
    (mul_nonneg hw (pow_nonneg (zero_le_one.trans hs) _)) (hC.trans hCC))

/-- `le_mul_of_decay` with an exponent depending on the index. -/
theorem le_mul_of_decay' {Ix X : Type*} [Fintype Ix] [Nonempty Ix] (Θ w s : X → ℝ)
    (Y : Ix → X → ℝ) (hΘ : ∀ g, 0 ≤ Θ g) (hw : ∀ g, 0 ≤ w g) (hs : ∀ g, 1 ≤ s g)
    (hY : ∀ i g, 0 ≤ Y i g)
    (hdec : ∀ i, ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ g, Θ g * (1 + Y i g) ^ k ≤ C * (w g * s g ^ m))
    (hH : ∃ C : ℝ, ∀ g, s g ≤ C * ∑ i, (1 + Y i g)) (n : ℕ) :
    ∃ B : ℝ, ∀ g, Θ g * s g ^ n ≤ B * w g := by
  classical
  obtain ⟨m, hm⟩ := exists_uniform (Finset.univ : Finset Ix)
    (fun i m k C => ∀ g, Θ g * (1 + Y i g) ^ k ≤ C * (w g * s g ^ m))
    (fun i m m' k C C' hmm hCC hC hP g => le_mul_mono (hw g) (hs g) hmm hCC hC (hP g))
    (fun i _ => by
      obtain ⟨m, hm⟩ := hdec i
      refine ⟨m, fun k => ?_⟩
      obtain ⟨C, hC⟩ := hm k
      refine ⟨max C 0, le_max_right _ _, fun g => (hC g).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (hw g) (pow_nonneg (zero_le_one.trans (hs g)) _)))
  exact le_mul_of_decay Θ w s Y m hΘ hw hs hY (fun i k => by
    obtain ⟨C, -, hC⟩ := hm k
    exact ⟨C, fun g => hC i (Finset.mem_univ i) g⟩) hH n

/-! ### The integral estimates -/

open Langlands.Analysis.AntiperiodicIntegralDecay in
/-- **The estimate on a cone.** Let `h` be smooth with compact support, `C'` a set containing the
`1`-thickening of its support, and `c_q`, `v_q` finitely many smooth functions and directions.
For every `k` there is `K` such that `‖∫ h E‖ (1 + R)^k ≤ K W` whenever `E = ∑_q c_q Φ_q` up to
`B W e^{-εR}` on `C'`, each continuous `Φ_q` is bounded by `B W` on `C'` and satisfies
`Φ_q(x + s v_q) = e^{i s Y} Φ_q(x)`, and `c R - C₁ ≤ Y`. -/
theorem exists_norm_integral_mul_one_add_pow_le_of_cone {n : ℕ} {mu : Measure (Fin n → ℝ)}
    [mu.IsAddRightInvariant] [IsFiniteMeasureOnCompacts mu] {h : (Fin n → ℝ) → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hsupp : HasCompactSupport h) {C' : Set (Fin n → ℝ)}
    (hC' : cthickening 1 (tsupport h) ⊆ C') {k₀ : ℕ} (c : Fin k₀ → (Fin n → ℝ) → ℂ)
    (hc : ∀ q, ContDiff ℝ (⊤ : ℕ∞) (c q)) (v : Fin k₀ → (Fin n → ℝ)) {ε cc C₁ B : ℝ}
    (hε : 0 < ε) (hcc : 0 < cc) (hB : 0 ≤ B) (k : ℕ) :
    ∃ K : ℝ, ∀ (E : (Fin n → ℝ) → ℂ) (Φ : Fin k₀ → (Fin n → ℝ) → ℂ) (Y R W : ℝ),
      Continuous E → (∀ q, Continuous (Φ q)) →
      (∀ q (s : ℝ) (x : Fin n → ℝ),
        Φ q (x + s • v q) = Complex.exp (Complex.I * (s * Y)) * Φ q x) →
      0 ≤ R → 0 ≤ W → cc * R - C₁ ≤ Y →
      (∀ q, ∀ x ∈ C', ‖Φ q x‖ ≤ B * W) →
      (∀ x ∈ C', ‖E x - ∑ q, c q x * Φ q x‖ ≤ B * W * Real.exp (-(ε * R))) →
      ‖∫ x, h x * E x ∂mu‖ * (1 + R) ^ k ≤ K * W := by
  obtain ⟨Cexp, hCexp⟩ := exists_one_add_pow_mul_exp_neg_le hε k
  have hk : ∀ q, ContDiff ℝ k (fun x => h x * c q x) := fun q =>
    (hh.mul (hc q)).of_le (by exact_mod_cast le_top)
  have hsq : ∀ q, HasCompactSupport (fun x => h x * c q x) := fun q => hsupp.mul_right
  choose Kq hKq using fun q => exists_norm_integral_mul_one_add_pow_le (mu := mu) k (hk q) (hsq q)
    (v q)
  set D : ℝ := 1 + (1 + |C₁|) / cc with hD
  set T : ℝ := ∫ x, ‖h x‖ ∂mu
  have hT0 : 0 ≤ T := integral_nonneg fun _ => norm_nonneg _
  refine ⟨B * T * |Cexp| + ∑ q, D ^ k * |Kq q| * B,
    fun E Φ Y R W hE hΦ hphase hR hW hY hΦb hrem => ?_⟩
  have hthick : ∀ q, cthickening 1 (tsupport (fun x => h x * c q x)) ⊆ C' := fun q =>
    (cthickening_subset_of_subset 1 (tsupport_mul_subset_left)).trans hC'
  have hcont_h : Continuous h := hh.continuous
  have hint_rem : Integrable (fun x => h x * (E x - ∑ q, c q x * Φ q x)) mu :=
    (hcont_h.mul (hE.sub (continuous_finsetSum _ fun q _ =>
      (hc q).continuous.mul (hΦ q)))).integrable_of_hasCompactSupport hsupp.mul_right
  have hint_q : ∀ q, Integrable (fun x => h x * c q x * Φ q x) mu := fun q =>
    ((hcont_h.mul (hc q).continuous).mul (hΦ q)).integrable_of_hasCompactSupport
      (hsq q).mul_right
  have hsplit : ∫ x, h x * E x ∂mu =
      ∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu + ∑ q, ∫ x, h x * c q x * Φ q x ∂mu := by
    rw [← integral_finsetSum _ fun q _ => hint_q q, ← integral_add hint_rem
      (integrable_finsetSum _ fun q _ => hint_q q)]
    congr 1
    funext x
    rw [Finset.sum_congr rfl fun q _ => (mul_assoc (h x) (c q x) (Φ q x)), ← Finset.mul_sum]
    ring
  -- the remainder
  have hrem' : ‖∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu‖ * (1 + R) ^ k ≤ B * T * |Cexp| * W := by
    have h1 := norm_integral_mul_le_of_bound (mu := mu) hcont_h hsupp
      (Φ := fun x => E x - ∑ q, c q x * Φ q x) (A := B * W * Real.exp (-(ε * R)))
      fun y hy => hrem y (hC' hy)
    calc ‖∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu‖ * (1 + R) ^ k
        ≤ (B * W * Real.exp (-(ε * R)) * T) * (1 + R) ^ k :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (by linarith) _)
      _ = B * T * W * ((1 + R) ^ k * Real.exp (-(ε * R))) := by ring
      _ ≤ B * T * W * |Cexp| :=
          mul_le_mul_of_nonneg_left ((hCexp R hR).trans (le_abs_self _)) (by positivity)
      _ = B * T * |Cexp| * W := by ring
  -- the components
  have hRY : (1 + R) ^ k ≤ D ^ k * (1 + |Y|) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith) ?_ k
    have hR' : R ≤ (|Y| + |C₁|) / cc := by
      rw [le_div_iff₀ hcc]
      have := le_abs_self Y
      have := le_abs_self C₁
      nlinarith
    have hD1 : (|Y| + |C₁|) / cc ≤ (1 + |C₁|) / cc * (1 + |Y|) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcc]
      nlinarith [abs_nonneg Y, abs_nonneg C₁]
    rw [hD]
    nlinarith [abs_nonneg Y]
  have hcomp : ∀ q, ‖∫ x, h x * c q x * Φ q x ∂mu‖ * (1 + R) ^ k ≤ D ^ k * |Kq q| * B * W := by
    intro q
    have h1 := hKq q (Φ q) Y (B * W) (hΦ q) (hphase q) (mul_nonneg hB hW)
      fun y hy => hΦb q y (hthick q hy)
    calc ‖∫ x, h x * c q x * Φ q x ∂mu‖ * (1 + R) ^ k
        ≤ ‖∫ x, h x * c q x * Φ q x ∂mu‖ * (D ^ k * (1 + |Y|) ^ k) :=
          mul_le_mul_of_nonneg_left hRY (norm_nonneg _)
      _ = D ^ k * (‖∫ x, h x * c q x * Φ q x ∂mu‖ * (1 + |Y|) ^ k) := by ring
      _ ≤ D ^ k * (Kq q * (B * W)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ D ^ k * (|Kq q| * (B * W)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg hB hW)) (by positivity)
      _ = D ^ k * |Kq q| * B * W := by ring
  rw [hsplit]
  calc ‖∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu + ∑ q, ∫ x, h x * c q x * Φ q x ∂mu‖ * (1 + R) ^ k
      ≤ (‖∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu‖ +
          ∑ q, ‖∫ x, h x * c q x * Φ q x ∂mu‖) * (1 + R) ^ k := by
        refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (pow_nonneg (by linarith) _)
        exact add_le_add_right (norm_sum_le _ _) _
    _ = ‖∫ x, h x * (E x - ∑ q, c q x * Φ q x) ∂mu‖ * (1 + R) ^ k +
          ∑ q, ‖∫ x, h x * c q x * Φ q x ∂mu‖ * (1 + R) ^ k := by
        rw [add_mul, Finset.sum_mul]
    _ ≤ B * T * |Cexp| * W + ∑ q, D ^ k * |Kq q| * B * W :=
        add_le_add hrem' (Finset.sum_le_sum fun q _ => hcomp q)
    _ = (B * T * |Cexp| + ∑ q, D ^ k * |Kq q| * B) * W := by
        rw [add_mul, Finset.sum_mul]

/-! ### Iwasawa subgroups for the standard parabolics of a setup -/

section Iwasawa

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- A compact subgroup that is Iwasawa for one minimal parabolic is Iwasawa for the standard
minimal parabolic of every algebraic Siegel setup: the two minimal parabolics are conjugate by a
rational point (`minimalParabolicConjugacy`). -/
theorem isIwasawaCompact_standardMinimal (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {K : Subgroup (AdelicGroupPoints F G)}
    (hP₀ : ∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) :
    IsIwasawaCompact (Standard.parabolicHom i ν ∅) K := by
  obtain ⟨P₀, _, p₀, _, hmin, hK⟩ := hP₀
  obtain ⟨s, e, he⟩ := minimalParabolicConjugacy F G hG P₀ _ p₀
    (Standard.parabolicHom i ν ∅) hmin hsetup.2.2.1
  have hconj : ∀ x, map F P₀ G (p₀ ≫ (G.innerIso s).hom) x =
      innerAdelicPoint F G s * map F P₀ G p₀ x * (innerAdelicPoint F G s)⁻¹ := by
    intro x
    rw [map_comp_apply_of_hom]
    exact affinePointsTarget_innerIso_hom F G s _
  have hK' : IsIwasawaCompact (p₀ ≫ (G.innerIso s).hom) K := hK.of_conjugate_map hconj
  refine hK'.of_range_eq ?_
  rw [he, SubgroupFunctor.range_iso_comp]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- An Iwasawa subgroup for the standard minimal parabolic is Iwasawa for every standard
parabolic `Q_J`. -/
theorem isIwasawaCompact_standard (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {K : Subgroup (AdelicGroupPoints F G)}
    (hK₀ : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) : IsIwasawaCompact (Standard.parabolicHom i ν J) K := by
  have hi : IsMaximalSplitTorus i := hsetup.1
  have hν : IsGenericCocharacter i ν := hsetup.2.1
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hOrder : standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
    ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
      (Set.empty_subset _)
  let inc := (Standard.isRepresentedBy_parabolicHom i ν ∅).inclusionHom
    (Standard.isRepresentedBy_parabolicHom i ν J) hOrder
  have hcomp : inc ≫ Standard.parabolicHom i ν J = Standard.parabolicHom i ν ∅ :=
    SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _
  exact IsIwasawaCompact.of_comp inc (hcomp.symm ▸ hK₀)

end Iwasawa

/-! ### Parameters, phases and continuity -/

section Parameters

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic TensorProduct

variable {F : Type} [Field F] [NumberField F]

/-- `⟨i x, Y⟩ = ⟨x, Y⟩ i` for a real parameter `x`. -/
theorem complexParameterPairing_imaginaryParameter {H : GroupScheme (Spec (CommRingCat.of F))}
    (x : RealCharacterParameter F H) (Y : RealCharacterDual F H) :
    complexParameterPairing F H (imaginaryParameter F H x) Y =
      (realParameterPairing F H x Y : ℂ) * Complex.I := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ =>
    change ((t : ℂ) * Complex.I) * (Y χ : ℂ) = ((t * Y χ : ℝ) : ℂ) * Complex.I
    simp only [Complex.ofReal_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Complex.ofReal_add, add_mul, hx, hy]

/-- A scalar function meromorphic in coordinates whose domain of holomorphy contains the
imaginary parameters is continuous on them, in any real coordinates. -/
theorem continuous_imaginary_of_isMeromorphic {P : GroupScheme (Spec (CommRingCat.of F))}
    {f : ComplexCharacterParameter F P → ℂ} {D : Set (ComplexCharacterParameter F P)}
    (hf : IsMeromorphicInCoordinatesOn f D) (hD : Set.range (imaginaryParameter F P) ⊆ D)
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Continuous fun x => f (imaginaryParameter F P (e x)) := by
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) := hf.1
  set m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let eC : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let Lx : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (eC.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ e.toLinearMap
  have hLx : Continuous Lx := LinearMap.continuous_of_finiteDimensional Lx
  have hq : ∀ x, eC (Lx x) = imaginaryParameter F P (e x) := fun x => by
    simp only [Lx, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  obtain ⟨hUo, -, hhol, -⟩ := hf.2 m eC
  have hcont : ContinuousOn (f ∘ eC) (eC ⁻¹' D) :=
    (differentiableOn_of_isHolomorphicOn hhol).continuousOn
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hx : Lx x ∈ eC ⁻¹' D := by
    rw [Set.mem_preimage, hq]
    exact hD ⟨e x, rfl⟩
  have := (hcont.continuousAt (hUo.mem_nhds hx)).comp hLx.continuousAt
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, hq]

end Parameters

/-! ### The phase law of Eisenstein series along the ambient characters -/

section Ambient

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic TensorProduct

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- **The ambient phase law.** Shifting the imaginary parameter of a continued Eisenstein series
by the pullback of `s ⊗ χ`, `χ` a rational character of `G`, multiplies its value at `g` by
`‖χ(g)‖^{is}` (the Library's `eisensteinAmbientShift_of_regularParameter`). -/
theorem eisenstein_ambient_phase (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (φ : AdelicGroupPoints F G → ℂ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (himag : Set.range (imaginaryParameter F P) ⊆ D)
    (hmero : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (χ : rationalCharacters G)
    (g : AdelicGroupPoints F G) (s : ℝ) (x : Fin n → ℝ) :
    E (imaginaryParameter F P
        (e (x + s • e.symm (realCharacterParameterPullback p ((1 : ℝ) ⊗ₜ[ℤ] χ))))) g =
      Complex.exp (Complex.I * (s * characterLog F G g χ)) *
        E (imaginaryParameter F P (e x)) g := by
  obtain ⟨R, hR⟩ := hreg
  have hw : s • realCharacterParameterPullback p ((1 : ℝ) ⊗ₜ[ℤ] χ) =
      realCharacterParameterPullback p (s ⊗ₜ[ℤ] χ) := by
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hsum : imaginaryParameter F P
      (e (x + s • e.symm (realCharacterParameterPullback p ((1 : ℝ) ⊗ₜ[ℤ] χ)))) =
      imaginaryParameter F P (e x) + parameterRestrict p (imaginaryParameter F G (s ⊗ₜ[ℤ] χ)) := by
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply, hw, map_add, imaginaryParameter_pullback]
  have hmem : imaginaryParameter F P (e x) +
      parameterRestrict p (imaginaryParameter F G (s ⊗ₜ[ℤ] χ)) ∈ D := by
    rw [← hsum]
    exact himag ⟨_, rfl⟩
  have hshift := (eisensteinAmbientShift_of_regularParameter eisensteinRegularParameter).2 F G P M
    A p l a r hA hT hG K hK φ g (fun lam => E lam g) D (hmero g)
    ⟨R, fun lam _ hlam => congrFun (hR lam hlam) g⟩
    (imaginaryParameter F G (s ⊗ₜ[ℤ] χ)) (parameterRealPart_imaginaryParameter _)
    (imaginaryParameter F P (e x)) (himag ⟨e x, rfl⟩) hmem
  rw [hsum, hshift]
  congr 1
  rw [parameterPower, complexParameterPairing_imaginaryParameter, realParameterPairing_tmul]
  push_cast
  ring_nf

end Ambient

/-! ### Chamber coordinates -/

section Chamber

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- On the weak chamber of threshold `t`, `log t ≤ log |β(b)|` for every simple root `β`. -/
theorem log_le_logNormHom_of_mem_chamber {t : ℝ≥0ˣ} {b : intrinsicSubgroup F T₀}
    (hb : b ∈ weakSimpleRootChamber F T₀ T j G i ν t) {β : characterLattice T}
    (hβ : β ∈ simpleRelativeRoots i ν) :
    Real.log ((t : ℝ≥0) : ℝ) ≤ logNormHom F T₀ b.val (j ≫ β) := by
  have h := hb β hβ
  have htpos : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by
    exact_mod_cast (Units.ne_zero t).bot_lt
  change Real.log ((t : ℝ≥0) : ℝ) ≤ Real.log ((normCharacter F T₀ (j ≫ β) b.val : ℝ≥0) : ℝ)
  exact Real.log_le_log htpos (by exact_mod_cast Units.val_le_val.mpr h)

/-- **The bounded case of the cone selection.** If every simple root satisfies
`log |β(b)| < δ₀ R` with `R = ∑_β |log |β(b)||` and `δ₀ = 1/(#Δ + 1)`, then `R` is bounded by
`#Δ (#Δ + 1) |log t|`. -/
theorem sum_abs_le_of_forall_lt {Δf : Finset (characterLattice T)} {t : ℝ≥0ˣ}
    {b : intrinsicSubgroup F T₀}
    (hlog : ∀ β ∈ Δf, Real.log ((t : ℝ≥0) : ℝ) ≤ logNormHom F T₀ b.val (j ≫ β))
    (hlt : ∀ β ∈ Δf, logNormHom F T₀ b.val (j ≫ β) <
      1 / ((Δf.card : ℝ) + 1) * ∑ y ∈ Δf, |logNormHom F T₀ b.val (j ≫ y)|) :
    ∑ y ∈ Δf, |logNormHom F T₀ b.val (j ≫ y)| ≤
      (Δf.card : ℝ) * ((Δf.card : ℝ) + 1) * |Real.log ((t : ℝ≥0) : ℝ)| := by
  set R := ∑ y ∈ Δf, |logNormHom F T₀ b.val (j ≫ y)|
  set c : ℝ := (Δf.card : ℝ)
  set L := |Real.log ((t : ℝ≥0) : ℝ)|
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hterm : ∀ β ∈ Δf, |logNormHom F T₀ b.val (j ≫ β)| ≤ 1 / (c + 1) * R + L := by
    intro β hβ
    rcases le_or_gt 0 (logNormHom F T₀ b.val (j ≫ β)) with h0 | h0
    · rw [abs_of_nonneg h0]
      have := hlt β hβ
      have : 0 ≤ L := abs_nonneg _
      linarith
    · rw [abs_of_neg h0]
      have h1 := hlog β hβ
      have h2 : -Real.log ((t : ℝ≥0) : ℝ) ≤ L := neg_le_abs _
      have hR0 : 0 ≤ 1 / (c + 1) * R :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      linarith
  have hsum : R ≤ c * (1 / (c + 1) * R + L) := by
    calc R ≤ ∑ _y ∈ Δf, (1 / (c + 1) * R + L) := Finset.sum_le_sum hterm
      _ = c * (1 / (c + 1) * R + L) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc1 : 0 < c + 1 := by linarith
  have : R / (c + 1) ≤ c * L := by
    have h' : R - c * (1 / (c + 1) * R) ≤ c * L := by linarith
    have : R - c * (1 / (c + 1) * R) = R / (c + 1) := by field_simp; ring
    linarith
  rw [div_le_iff₀ hc1] at this
  linarith

end Chamber

/-- The norm of the integral of a finite sum of integrable terms. -/
theorem norm_integral_sum_le {n kk : ℕ} {mu : Measure (Fin n → ℝ)}
    (f : Fin kk → (Fin n → ℝ) → ℂ) (hint : ∀ q, Integrable (f q) mu) :
    ‖∫ x, ∑ q, f q x ∂mu‖ ≤ ∑ q, ‖∫ x, f q x ∂mu‖ := by
  rw [integral_finsetSum _ fun q _ => hint q]
  exact norm_sum_le _ _

/-! ### The chamber estimate -/

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus TensorProduct
  Langlands.Analysis.AntiperiodicIntegralDecay in
/-- **The chamber estimate from the weak constant term.** For a wave packet
`Θ = ∫ ∑_q c_q(x) E_q(i e(x)) dx`, write `R(b) = ∑_β |log |β(b)||` and `Y_k = log ‖χ_k(z b ω)‖`
for the characters `χ_k` of `SiegelChamberHeightComparisonStatement`. The ambient phase law and
Proposition 4.1 give `‖Θ‖ (1 + |Y_k|)^N ≪ δ^{1/2} σ^m` for every `N`. On the cone of a proper
`J ⊆ Δ` (the simple roots outside `J` are at least `R / (#Δ + 1)`), the decomposition of
`EisensteinWeakConstantTermApproximationStatement`, the growth of `H_{Q_J}` from
`StandardParabolicConeHeightStatement` and the finite-difference estimate give
`‖Θ‖ (1 + R)^N ≪ δ^{1/2} σ^m`; every point with `R` large lies on such a cone. The height
comparison `σ ≪ 1 + R + ∑_k |Y_k|` then gives `‖Θ‖ ≪ δ^{1/2} σ^{-n}`. -/
theorem wavePacketChamberDecay_of_weakConstantTerm
    (hW : EisensteinWeakConstantTermApproximationStatement)
    (hU : EisensteinUniformTemperednessStatement)
    (hGeo : SiegelChamberGeometryStatement) : WavePacketChamberDecayStatement := by
  classical
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ T i ν T₀ j hsetup t Ω hΩ n
  have hK₀ := isIwasawaCompact_standardMinimal hG hsetup hP₀
  obtain ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU', hK, nn, e, kk, v,
    c, E, D, hv, hc, himag, hmero, hreg, rfl⟩ := hΘ
  -- the spectral measure
  have hctop : (ENNReal.ofReal (2 * Real.pi))⁻¹ ^ nn ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne')
  have : IsFiniteMeasureOnCompacts (spectralMeasure nn) :=
    IsFiniteMeasureOnCompacts.smul (volume : Measure (Fin nn → ℝ)) hctop
  have : (spectralMeasure nn).IsAddRightInvariant := by
    unfold spectralMeasure
    infer_instance
  -- the compact set of parameters
  set C' : Set (Fin nn → ℝ) := cthickening 1 (⋃ q, tsupport (c q)) with hC'def
  have hC' : IsCompact C' := (isCompact_iUnion fun q => (hc q).2).cthickening
  have hsub : ∀ q, cthickening 1 (tsupport (c q)) ⊆ C' := fun q =>
    cthickening_subset_of_subset 1 (subset_iUnion (fun q => tsupport (c q)) q)
  -- points
  let X := {g : AdelicGroupPoints F G × PositiveRealTorus.intrinsicSubgroup F T₀ ×
      AdelicGroupPoints F G // g.1 ∈ RestrictionSplitCentre.canonicalSubgroup F G ∧
      g.2.1 ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧ g.2.2 ∈ Ω}
  let pt : X → AdelicGroupPoints F G := fun g =>
    g.1.1 * positiveMap F G T i T₀ j g.1.2.1 * g.1.2.2
  let wv : X → ℝ := fun g => Real.sqrt (siegelModulus F G T i ν T₀ j g.1.2.1)
  let sv : X → ℝ := fun g => adelicLogHeight F G rho (pt g)
  have hw0 : ∀ g, 0 ≤ wv g := fun g => Real.sqrt_nonneg _
  have hs1 : ∀ g, 1 ≤ sv g := fun g => one_le_adelicLogHeight rho _
  have hWS : ∀ (g : X) (m : ℕ), 0 ≤ wv g * sv g ^ m := fun g m =>
    mul_nonneg (hw0 g) (pow_nonneg (zero_le_one.trans (hs1 g)) _)
  -- continuity and integrability
  have hEc : ∀ q (g : AdelicGroupPoints F G),
      Continuous fun x => E q (imaginaryParameter F P (e x)) g := fun q g =>
    continuous_imaginary_of_isMeromorphic (hmero q g) himag e
  have hint : ∀ q (g : AdelicGroupPoints F G),
      Integrable (fun x => c q x * E q (imaginaryParameter F P (e x)) g) (spectralMeasure nn) :=
    fun q g => ((hc q).1.continuous.mul (hEc q g)).integrable_of_hasCompactSupport
      (hc q).2.mul_right
  -- uniform temperedness
  have hU4 : ∀ q, ∃ (m : ℕ) (B : ℝ), ∀ x ∈ C', ∀ g : X,
      ‖E q (imaginaryParameter F P (e x)) (pt g)‖ ≤ |B| * (wv g * sv g ^ m) := fun q => by
    obtain ⟨m, hm⟩ := hU F G P M U A p iU l a r hA hT hG hU' K hK rho hsmooth hcalc (v q) hKmax
      hrho (hv q) (E q) D himag (hmero q) (hreg q) nn e C' hC'
    obtain ⟨B, hB⟩ := hm T i ν T₀ j hsetup t Ω hΩ
    refine ⟨m, B, fun x hx g => (hB x hx g.1.1 g.2.1 g.1.2.1 g.2.2.1 g.1.2.2 g.2.2.2).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (hWS g m)
  choose mU BU hUb using hU4
  set mT : ℕ := ∑ q, mU q with hmT
  have hmTle : ∀ q, mU q ≤ mT := fun q =>
    Finset.single_le_sum (f := mU) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  -- the packet as a finite sum
  have hsplit : ∀ g : X, ‖∫ x, ∑ q, c q x * E q (imaginaryParameter F P (e x)) (pt g)
      ∂spectralMeasure nn‖ ≤ ∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
      ∂spectralMeasure nn‖ := fun g =>
    norm_integral_sum_le (fun q x => c q x * E q (imaginaryParameter F P (e x)) (pt g))
      fun q => hint q (pt g)
  -- the trivial bound
  have htriv : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : X, ∀ q,
      ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g) ∂spectralMeasure nn‖ ≤
        C * (wv g * sv g ^ mT) := by
    refine ⟨∑ q, |BU q| * ∫ x, ‖c q x‖ ∂spectralMeasure nn,
      Finset.sum_nonneg fun q _ => mul_nonneg (abs_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _), fun g q => ?_⟩
    have h1 := norm_integral_mul_le_of_bound (mu := spectralMeasure nn) (hc q).1.continuous
      (hc q).2 (Φ := fun x => E q (imaginaryParameter F P (e x)) (pt g))
      (A := |BU q| * (wv g * sv g ^ mU q)) fun y hy => hUb q y (hsub q hy) g
    refine h1.trans ?_
    have hT0 : 0 ≤ ∫ x, ‖c q x‖ ∂spectralMeasure nn := integral_nonneg fun _ => norm_nonneg _
    calc |BU q| * (wv g * sv g ^ mU q) * ∫ x, ‖c q x‖ ∂spectralMeasure nn
        ≤ |BU q| * (wv g * sv g ^ mT) * ∫ x, ‖c q x‖ ∂spectralMeasure nn :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_pow_le_mul_pow (hw0 g) (hs1 g) (hmTle q)) (abs_nonneg _)) hT0
      _ = (|BU q| * ∫ x, ‖c q x‖ ∂spectralMeasure nn) * (wv g * sv g ^ mT) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (hWS g mT)
          exact Finset.single_le_sum (f := fun q => |BU q| * ∫ x, ‖c q x‖ ∂spectralMeasure nn)
            (fun q _ => mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => norm_nonneg _))
            (Finset.mem_univ q)
  obtain ⟨Ctr, hCtr0, hCtr⟩ := htriv
  -- the central characters and the height comparison
  obtain ⟨r', χ, CH, hCH⟩ := hGeo.2 F G hG rho hrho T i ν T₀ j hsetup Ω hΩ
  -- the simple roots
  have hΔfin : (simpleRelativeRoots i ν).Finite :=
    hsetup.1.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  set Δf := hΔfin.toFinset with hΔf
  have hmemΔ : ∀ β, β ∈ Δf ↔ β ∈ simpleRelativeRoots i ν := fun β => hΔfin.mem_toFinset
  let Rb : PositiveRealTorus.intrinsicSubgroup F T₀ → ℝ := fun b =>
    ∑ β ∈ Δf, |logNormHom F T₀ b.val (j ≫ β)|
  have hRb0 : ∀ b, 0 ≤ Rb b := fun b => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hRbge : ∀ b, ∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ b.val (j ≫ β)| ≤ Rb b :=
    fun b β hβ => Finset.single_le_sum (f := fun β => |logNormHom F T₀ b.val (j ≫ β)|)
      (fun _ _ => abs_nonneg _) ((hmemΔ β).2 hβ)
  let Yv : Option (Fin r') → X → ℝ := fun o g =>
    o.elim (Rb g.1.2.1) fun q => |characterLog F G (pt g) (χ q)|
  have hY0 : ∀ o g, 0 ≤ Yv o g := by
    intro o g
    cases o with
    | none => exact hRb0 _
    | some q => exact abs_nonneg _
  let Θv : X → ℝ := fun g =>
    ‖∫ x, ∑ q, c q x * E q (imaginaryParameter F P (e x)) (pt g) ∂spectralMeasure nn‖
  have hΘ0 : ∀ g, 0 ≤ Θv g := fun g => norm_nonneg _
  have hck : ∀ q (k : ℕ), ContDiff ℝ k (c q) := fun q k =>
    (hc q).1.of_le (by exact_mod_cast le_top)
  -- decay along the central characters
  have hcentral : ∀ q' : Fin r', ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ g : X,
      Θv g * (1 + |characterLog F G (pt g) (χ q')|) ^ k ≤ C * (wv g * sv g ^ m) := by
    intro q'
    refine ⟨mT, fun k => ?_⟩
    choose Kq hKq using fun q => exists_norm_integral_mul_one_add_pow_le
      (mu := spectralMeasure nn) k (hck q k) (hc q).2
      (e.symm (realCharacterParameterPullback p ((1 : ℝ) ⊗ₜ[ℤ] χ q')))
    refine ⟨∑ q, |Kq q| * |BU q|, fun g => ?_⟩
    have hpow0 : 0 ≤ (1 + |characterLog F G (pt g) (χ q')|) ^ k := by positivity
    have hterm : ∀ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
        ∂spectralMeasure nn‖ * (1 + |characterLog F G (pt g) (χ q')|) ^ k ≤
        |Kq q| * |BU q| * (wv g * sv g ^ mT) := by
      intro q
      have h1 := hKq q (fun x => E q (imaginaryParameter F P (e x)) (pt g))
        (characterLog F G (pt g) (χ q')) (|BU q| * (wv g * sv g ^ mU q)) (hEc q (pt g))
        (fun s x => eisenstein_ambient_phase r hA hT hG hK (v q) himag (hmero q) (hreg q) e
          (χ q') (pt g) s x)
        (mul_nonneg (abs_nonneg _) (hWS g _)) fun y hy => hUb q y (hsub q hy) g
      refine h1.trans ?_
      calc Kq q * (|BU q| * (wv g * sv g ^ mU q)) ≤ |Kq q| * (|BU q| * (wv g * sv g ^ mU q)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (abs_nonneg _) (hWS g _))
        _ ≤ |Kq q| * (|BU q| * (wv g * sv g ^ mT)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
              (abs_nonneg _)
            exact mul_pow_le_mul_pow (hw0 g) (hs1 g) (hmTle q)
        _ = |Kq q| * |BU q| * (wv g * sv g ^ mT) := by ring
    calc Θv g * (1 + |characterLog F G (pt g) (χ q')|) ^ k
        ≤ (∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
            ∂spectralMeasure nn‖) * (1 + |characterLog F G (pt g) (χ q')|) ^ k :=
          mul_le_mul_of_nonneg_right (hsplit g) hpow0
      _ = ∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
            ∂spectralMeasure nn‖ * (1 + |characterLog F G (pt g) (χ q')|) ^ k :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ q, |Kq q| * |BU q| * (wv g * sv g ^ mT) := Finset.sum_le_sum fun q _ => hterm q
      _ = (∑ q, |Kq q| * |BU q|) * (wv g * sv g ^ mT) := (Finset.sum_mul _ _ _).symm
  -- decay on the cones
  set δ₀ : ℝ := 1 / ((Δf.card : ℝ) + 1) with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hcone : ∀ Jj ∈ (Δf.powerset.erase Δf) ×ˢ (Finset.univ : Finset (Fin kk)),
      ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : X,
        (∀ α ∈ Δf, α ∉ Jj.1 → δ₀ * Rb g.1.2.1 ≤ logNormHom F T₀ g.1.2.1.val (j ≫ α)) →
        ‖∫ x, c Jj.2 x * E Jj.2 (imaginaryParameter F P (e x)) (pt g) ∂spectralMeasure nn‖ *
          (1 + Rb g.1.2.1) ^ k ≤ C * (wv g * sv g ^ m) := by
    rintro ⟨J, jj⟩ hJj
    obtain ⟨hJ, -⟩ := Finset.mem_product.mp hJj
    have hJsub' : J ⊆ Δf := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hJ)
    have hJne : J ≠ Δf := Finset.ne_of_mem_erase hJ
    have hJsub : (↑J : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
      fun β hβ => (hmemΔ β).1 (hJsub' hβ)
    obtain ⟨α, hαΔ, hαJ⟩ : ∃ α ∈ Δf, α ∉ J := by
      by_contra h
      push Not at h
      exact hJne (Finset.Subset.antisymm hJsub' h)
    have hJne' : ∃ α ∈ simpleRelativeRoots i ν, α ∉ (↑J : Set (characterLattice T)) :=
      ⟨α, (hmemΔ α).1 hαΔ, by exact_mod_cast hαJ⟩
    have hKQ := isIwasawaCompact_standard hG hsetup hK₀ hJsub
    have : IsClosedImmersion (Standard.parabolicHom i ν (↑J : Set _)).hom.hom.left :=
      Standard.isClosedSubgroup_parabolicHom i ν _
    have : IsAffineHom (Standard.parabolicScheme i ν (↑J : Set _)).X.hom :=
      (Standard.isClosedSubgroup_parabolicHom i ν _).isAffineHom
    have : IsAffine (Standard.parabolicScheme i ν (↑J : Set _)).X.left :=
      isAffine_of_isAffineHom (Standard.parabolicScheme i ν _).X.hom
    obtain ⟨ε, m, B, k₀, cW, V, L, Φ, hε, hcW, hL, hshift, hΦc, hΦb, hrem⟩ :=
      hW F G P M U A p iU l a r hA hT hG hU' K hK rho hsmooth hcalc (v jj) hKmax hrho (hv jj)
        (E jj) D himag (hmero jj) (hreg jj) nn e C' hC' T i ν T₀ j hsetup hK₀ (↑J) hJsub hJne'
        hKQ δ₀ hδ₀ t Ω hΩ
    obtain ⟨wt, cc, C₁, hcc, hH1⟩ :=
      hGeo.1 F G hG K T i ν T₀ j hsetup (↑J) hJsub hJne' hKQ δ₀ hδ₀ t Ω hΩ
    choose v₀ hv₀ using fun q' => hL q' wt
    refine ⟨m, fun k => ?_⟩
    obtain ⟨Kc, hKc⟩ := exists_norm_integral_mul_one_add_pow_le_of_cone
      (mu := spectralMeasure nn) (hc jj).1 (hc jj).2 (hsub jj) cW hcW
      (fun q' => (v₀ q' : Fin nn → ℝ)) (C₁ := C₁) hε hcc (abs_nonneg B) k
    refine ⟨max Kc 0, le_max_right _ _, fun g hconeg => ?_⟩
    have hβR : ∀ β ∈ simpleRelativeRoots i ν,
        |logNormHom F T₀ g.1.2.1.val (j ≫ β)| ≤ Rb g.1.2.1 := hRbge _
    have hαR : ∀ α ∈ simpleRelativeRoots i ν, α ∉ (↑J : Set (characterLattice T)) →
        δ₀ * Rb g.1.2.1 ≤ logNormHom F T₀ g.1.2.1.val (j ≫ α) :=
      fun α hα hαJ => hconeg α ((hmemΔ α).2 hα) (by exact_mod_cast hαJ)
    have hphase : ∀ q' (s : ℝ) (x : Fin nn → ℝ),
        Φ q' (x + s • (v₀ q' : Fin nn → ℝ)) (pt g) = Complex.exp (Complex.I *
          (s * realParameterPairing F _ wt (hKQ.height (pt g)))) * Φ q' x (pt g) := by
      intro q' s x
      have h := hshift q' (s • v₀ q') x (pt g)
      rw [Submodule.coe_smul] at h
      rw [h, map_smul, hv₀ q', IsIwasawaCompact.heightPower,
        complexParameterPairing_imaginaryParameter, map_smul, LinearMap.smul_apply, smul_eq_mul]
      congr 1
      push_cast
      ring_nf
    have hmain := hKc (fun x => E jj (imaginaryParameter F P (e x)) (pt g))
      (fun q' x => Φ q' x (pt g)) (realParameterPairing F _ wt (hKQ.height (pt g)))
      (Rb g.1.2.1) (wv g * sv g ^ m) (hEc jj (pt g)) (fun q' => hΦc q' (pt g)) hphase
      (hRb0 _) (hWS g m)
      (hH1 g.1.1 g.2.1 g.1.2.1 g.2.2.1 g.1.2.2 g.2.2.2 (Rb g.1.2.1) hβR hαR)
      (fun q' x hx => (hΦb q' x hx g.1.1 g.2.1 g.1.2.1 g.2.2.1 g.1.2.2 g.2.2.2).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self B) (hWS g m)))
      (fun x hx => (hrem x hx g.1.1 g.2.1 g.1.2.1 g.2.2.1 g.1.2.2 g.2.2.2 (Rb g.1.2.1) hβR
        hαR).trans (by
          have hsm : 1 ≤ sv g ^ m := one_le_pow₀ (hs1 g)
          have hexp : 0 ≤ Real.exp (-(ε * Rb g.1.2.1)) := (Real.exp_pos _).le
          have h1 : B * wv g ≤ |B| * (wv g * sv g ^ m) := by
            calc B * wv g ≤ |B| * wv g := mul_le_mul_of_nonneg_right (le_abs_self B) (hw0 g)
              _ = |B| * (wv g * 1) := by ring
              _ ≤ |B| * (wv g * sv g ^ m) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsm (hw0 g)) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right h1 hexp))
    exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hWS g m))
  obtain ⟨mC, hmC⟩ := exists_uniform ((Δf.powerset.erase Δf) ×ˢ (Finset.univ : Finset (Fin kk)))
    (fun Jj m k C => ∀ g : X,
        (∀ α ∈ Δf, α ∉ Jj.1 → δ₀ * Rb g.1.2.1 ≤ logNormHom F T₀ g.1.2.1.val (j ≫ α)) →
        ‖∫ x, c Jj.2 x * E Jj.2 (imaginaryParameter F P (e x)) (pt g) ∂spectralMeasure nn‖ *
          (1 + Rb g.1.2.1) ^ k ≤ C * (wv g * sv g ^ m))
    (fun Jj m m' k C C' hmm hCC hC hP g hg => le_mul_mono (hw0 g) (hs1 g) hmm hCC hC (hP g hg))
    hcone
  -- decay in the chamber coordinates
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ,
      R₀ = (Δf.card : ℝ) * ((Δf.card : ℝ) + 1) * |Real.log ((t : ℝ≥0) : ℝ)| := ⟨_, rfl⟩
  have hR0' : 0 ≤ R₀ := by
    rw [hR₀]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by linarith [(Nat.cast_nonneg Δf.card : (0 : ℝ) ≤ Δf.card)])) (abs_nonneg _)
  have hnone : ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ g : X,
      Θv g * (1 + Rb g.1.2.1) ^ k ≤ C * (wv g * sv g ^ m) := by
    refine ⟨max mC mT, fun k => ?_⟩
    obtain ⟨CC, hCC0, hCC⟩ := hmC k
    refine ⟨(kk : ℝ) * CC + (1 + R₀) ^ k * ((kk : ℝ) * Ctr), fun g => ?_⟩
    have hsumtriv : Θv g ≤ (kk : ℝ) * Ctr * (wv g * sv g ^ mT) := by
      refine (hsplit g).trans ?_
      calc ∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g) ∂spectralMeasure nn‖
          ≤ ∑ _q : Fin kk, Ctr * (wv g * sv g ^ mT) := Finset.sum_le_sum fun q _ => hCtr g q
        _ = (kk : ℝ) * Ctr * (wv g * sv g ^ mT) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hmono1 : wv g * sv g ^ mT ≤ wv g * sv g ^ max mC mT :=
      mul_pow_le_mul_pow (hw0 g) (hs1 g) (le_max_right _ _)
    have hmono2 : wv g * sv g ^ mC ≤ wv g * sv g ^ max mC mT :=
      mul_pow_le_mul_pow (hw0 g) (hs1 g) (le_max_left _ _)
    have hpos1 : 0 ≤ (kk : ℝ) * CC * (wv g * sv g ^ max mC mT) := by
      have := hWS g (max mC mT); positivity
    have hpos2 : 0 ≤ (1 + R₀) ^ k * ((kk : ℝ) * Ctr) * (wv g * sv g ^ max mC mT) := by
      have := hWS g (max mC mT); positivity
    by_cases hR : Rb g.1.2.1 ≤ R₀
    · have hpow : (1 + Rb g.1.2.1) ^ k ≤ (1 + R₀) ^ k :=
        pow_le_pow_left₀ (by linarith [hRb0 g.1.2.1]) (by linarith) k
      calc Θv g * (1 + Rb g.1.2.1) ^ k ≤ ((kk : ℝ) * Ctr * (wv g * sv g ^ mT)) * (1 + R₀) ^ k :=
            mul_le_mul hsumtriv hpow (pow_nonneg (by linarith [hRb0 g.1.2.1]) _)
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCtr0) (hWS g mT))
        _ ≤ (1 + R₀) ^ k * ((kk : ℝ) * Ctr) * (wv g * sv g ^ max mC mT) := by
            rw [show (kk : ℝ) * Ctr * (wv g * sv g ^ mT) * (1 + R₀) ^ k =
              (1 + R₀) ^ k * ((kk : ℝ) * Ctr) * (wv g * sv g ^ mT) by ring]
            exact mul_le_mul_of_nonneg_left hmono1 (by positivity)
        _ ≤ _ := by rw [add_mul]; linarith
    · push Not at hR
      set J := Δf.filter fun β => logNormHom F T₀ g.1.2.1.val (j ≫ β) < δ₀ * Rb g.1.2.1
        with hJdef
      have hlog : ∀ β ∈ Δf, Real.log ((t : ℝ≥0) : ℝ) ≤ logNormHom F T₀ g.1.2.1.val (j ≫ β) :=
        fun β hβ => log_le_logNormHom_of_mem_chamber g.2.2.1 ((hmemΔ β).1 hβ)
      have hJmem : J ∈ Δf.powerset.erase Δf := by
        refine Finset.mem_erase.mpr ⟨fun hJΔ => ?_, Finset.mem_powerset.mpr
          (Finset.filter_subset _ _)⟩
        have hall : ∀ β ∈ Δf, logNormHom F T₀ g.1.2.1.val (j ≫ β) <
            1 / ((Δf.card : ℝ) + 1) * ∑ y ∈ Δf, |logNormHom F T₀ g.1.2.1.val (j ≫ y)| := by
          intro β hβ
          rw [← hJΔ] at hβ
          exact (Finset.mem_filter.mp hβ).2
        have := sum_abs_le_of_forall_lt hlog hall
        rw [← hR₀] at this
        exact absurd this (not_le.mpr hR)
      have hconeJ : ∀ α ∈ Δf, α ∉ J →
          δ₀ * Rb g.1.2.1 ≤ logNormHom F T₀ g.1.2.1.val (j ≫ α) := by
        intro α hα hαJ
        by_contra hlt
        push Not at hlt
        exact hαJ (Finset.mem_filter.mpr ⟨hα, hlt⟩)
      have hterm : ∀ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
          ∂spectralMeasure nn‖ * (1 + Rb g.1.2.1) ^ k ≤ CC * (wv g * sv g ^ max mC mT) := by
        intro q
        refine (hCC (J, q) (Finset.mem_product.mpr ⟨hJmem, Finset.mem_univ q⟩) g hconeJ).trans ?_
        exact mul_le_mul_of_nonneg_left hmono2 hCC0
      calc Θv g * (1 + Rb g.1.2.1) ^ k
          ≤ (∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
              ∂spectralMeasure nn‖) * (1 + Rb g.1.2.1) ^ k :=
            mul_le_mul_of_nonneg_right (hsplit g) (pow_nonneg (by linarith [hRb0 g.1.2.1]) _)
        _ = ∑ q, ‖∫ x, c q x * E q (imaginaryParameter F P (e x)) (pt g)
              ∂spectralMeasure nn‖ * (1 + Rb g.1.2.1) ^ k := Finset.sum_mul _ _ _
        _ ≤ ∑ _q : Fin kk, CC * (wv g * sv g ^ max mC mT) := Finset.sum_le_sum fun q _ => hterm q
        _ = (kk : ℝ) * CC * (wv g * sv g ^ max mC mT) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ _ := by rw [add_mul]; linarith
  -- the height comparison
  have hH : ∃ C : ℝ, ∀ g : X, sv g ≤ C * ∑ o, (1 + Yv o g) := by
    refine ⟨|CH|, fun g => ?_⟩
    obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = Rb g.1.2.1 + ∑ q, |characterLog F G (pt g) (χ q)| :=
      ⟨_, rfl⟩
    have hR'0 : 0 ≤ R' := by
      rw [hR']; exact add_nonneg (hRb0 _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hsum0 : 0 ≤ ∑ q, |characterLog F G (pt g) (χ q)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hβ' : ∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ g.1.2.1.val (j ≫ β)| ≤ R' := by
      intro β hβ
      rw [hR']
      exact (hRbge _ β hβ).trans (le_add_of_nonneg_right hsum0)
    have hχ' : ∀ q, |characterLog F G (pt g) (χ q)| ≤ R' := by
      intro q
      rw [hR']
      exact (Finset.single_le_sum (f := fun q => |characterLog F G (pt g) (χ q)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ q)).trans (le_add_of_nonneg_left (hRb0 _))
    have h1 := hCH g.1.1 g.2.1 g.1.2.1 g.1.2.2 g.2.2.2 R' hR'0 hβ' hχ'
    have h2 : 1 + R' ≤ ∑ o, (1 + Yv o g) := by
      rw [Fintype.sum_option]
      have e1 : (1 + Yv none g) = 1 + Rb g.1.2.1 := rfl
      have e2 : ∀ q, (1 + Yv (some q) g) = 1 + |characterLog F G (pt g) (χ q)| := fun q => rfl
      rw [e1, Finset.sum_congr rfl fun q _ => e2 q, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hR']
      have : (0 : ℝ) ≤ (r' : ℝ) * 1 := by rw [mul_one]; exact Nat.cast_nonneg _
      linarith
    calc sv g ≤ CH * (1 + R') := h1
      _ ≤ |CH| * (1 + R') := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |CH| * ∑ o, (1 + Yv o g) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  -- combination
  have hdec : ∀ o, ∃ m : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ g : X,
      Θv g * (1 + Yv o g) ^ k ≤ C * (wv g * sv g ^ m) := by
    intro o
    cases o with
    | none => exact hnone
    | some q => exact hcentral q
  obtain ⟨Bf, hBf⟩ := le_mul_of_decay' Θv wv sv Yv hΘ0 hw0 hs1 hY0 hdec hH n
  refine ⟨Bf, fun z hz b hb ω hω => ?_⟩
  have hg := hBf ⟨(z, b, ω), hz, hb, hω⟩
  have hspos : 0 < adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ n :=
    pow_pos (lt_of_lt_of_le one_pos (one_le_adelicLogHeight rho _)) n
  rw [le_div_iff₀ hspos]
  exact hg


end Langlands.Global.ChamberDecay

namespace Langlands.Global

/-- **The chamber estimate from the weak constant term.**
`EisensteinWeakConstantTermApproximationStatement` (Delorme 2023, Lemma 5.3 with (4.3), (4.1)
and Proposition 4.1 for the Levi subgroups),
`EisensteinUniformTemperednessStatement` (Proposition 4.1) and `SiegelChamberGeometryStatement`
imply `WavePacketChamberDecayStatement` (Delorme 2023, (5.2) in the proof of Proposition 5.4). -/
def WavePacketChamberDecayReductionStatement : Prop :=
  EisensteinWeakConstantTermApproximationStatement → EisensteinUniformTemperednessStatement →
    SiegelChamberGeometryStatement → WavePacketChamberDecayStatement

theorem wavePacketChamberDecayReduction : WavePacketChamberDecayReductionStatement :=
  fun hW hU hGeo => ChamberDecay.wavePacketChamberDecay_of_weakConstantTerm hW hU hGeo

/-- `WavePacketSiegelDecayStatement` from joint continuity on the imaginary axis and the three
inputs of `WavePacketChamberDecayReductionStatement`. -/
theorem wavePacketSiegelDecay_of_weakConstantTerm
    (hcont : EisensteinImaginaryJointContinuityStatement)
    (hW : EisensteinWeakConstantTermApproximationStatement)
    (hU : EisensteinUniformTemperednessStatement)
    (hGeo : SiegelChamberGeometryStatement) : WavePacketSiegelDecayStatement :=
  wavePacketSiegelDecay_of_reduction hcont (wavePacketChamberDecayReduction hW hU hGeo)

end Langlands.Global
