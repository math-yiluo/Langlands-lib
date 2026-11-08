import Langlands.HarmonicAnalysis.GroupAction
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential decay of the positive part of a constant term

The analytic core of Waldspurger's Lemma VI.2.3, in an abstract form with explicit hypotheses.
A family of functions `F i` on a group `G`, annihilated by `p_i(ρ(a))` for right translation
`ρ(a)` and monic polynomials `p_i` of a fixed degree whose roots have modulus at most `θ < 1`,
and bounded by `C₁ B(g) (1 + σ(g))^d` on a translate of a chamber, decays like
`B(g) e^{-ε |H(g)|}` on the cone `{⟨α, H(g)⟩ ≥ δ |H(g)|}`.

* `rootPowerPolynomial p q` is `∏ (X - z^q)` over the roots `z` of `p` (with multiplicity);
  if `p(T)` kills `w` then so does `rootPowerPolynomial p q (T^q)`.
* `norm_le_of_linearRecurrence`: a linear recurrence with coefficients
  `|c_k| ≤ 2^{-(N-k)}/N` propagates the bound `K 2^{-n}` from the first `N` terms to all terms.
* `norm_le_of_aeval_eq_zero`: the same along the powers of `b` for a function annihilated by
  `p(ρ(b))` (estimate (2) of the source's proof).
* `exists_norm_le_exp_of_aeval_eq_zero`: the abstract Lemma VI.2.3.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis

section RootPower

/-- `∏ (X - z^q)`, the product over the roots `z` of `p` counted with multiplicity: the
polynomial whose roots are the `q`-th powers of the roots of `p`. -/
def rootPowerPolynomial (p : ℂ[X]) (q : ℕ) : ℂ[X] :=
  ((p.roots.map fun z => z ^ q).map fun w => X - C w).prod

theorem rootPowerPolynomial_monic (p : ℂ[X]) (q : ℕ) : (rootPowerPolynomial p q).Monic :=
  monic_multisetProd_X_sub_C _

theorem natDegree_rootPowerPolynomial (p : ℂ[X]) (q : ℕ) :
    (rootPowerPolynomial p q).natDegree = p.natDegree := by
  rw [rootPowerPolynomial, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map,
    IsAlgClosed.card_roots_eq_natDegree]

/-- A monic complex polynomial `p` divides `rootPowerPolynomial p q` composed with `X^q`. -/
theorem dvd_rootPowerPolynomial_comp {p : ℂ[X]} (hp : p.Monic) (q : ℕ) :
    p ∣ (rootPowerPolynomial p q).comp (X ^ q) := by
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
    IsAlgClosed.card_roots_eq_natDegree]
  rw [rootPowerPolynomial, multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  refine Multiset.prod_dvd_prod_of_dvd _ _ fun z _ => ?_
  simp only [Function.comp_apply, sub_comp, X_comp, C_comp]
  rw [C_pow]
  exact sub_dvd_pow_sub_pow X (C z) q

/-- If `p(T)` kills `w` for a monic `p`, then `rootPowerPolynomial p q (T^q)` kills `w`. -/
theorem aeval_rootPowerPolynomial_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) {p : ℂ[X]} (hp : p.Monic) (q : ℕ) {w : W}
    (h : aeval T p w = 0) : aeval (T ^ q) (rootPowerPolynomial p q) w = 0 := by
  obtain ⟨s, hs⟩ := dvd_rootPowerPolynomial_comp hp q
  have e : aeval (T ^ q) (rootPowerPolynomial p q) =
      aeval T ((rootPowerPolynomial p q).comp (X ^ q)) := by
    rw [aeval_comp, map_pow, aeval_X]
  rw [e, hs, mul_comm, map_mul, Module.End.mul_apply, h, map_zero]

/-- A product of complex numbers of modulus at most `η ≥ 0` has modulus at most `η^card`. -/
theorem norm_multiset_prod_le_pow {t : Multiset ℂ} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ z ∈ t, ‖z‖ ≤ η) : ‖t.prod‖ ≤ η ^ Multiset.card t := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons z t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (hη z (Multiset.mem_cons_self z t))
      (ih fun w hw => hη w (Multiset.mem_cons_of_mem hw)) (norm_nonneg _) hη0

/-- Elementary symmetric functions of complex numbers of modulus at most `η ≥ 0`. -/
theorem norm_esymm_le {s : Multiset ℂ} {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ z ∈ s, ‖z‖ ≤ η)
    (j : ℕ) : ‖s.esymm j‖ ≤ 2 ^ Multiset.card s * η ^ j := by
  rw [Multiset.esymm]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  have h1 : ((s.powersetCard j).map (norm ∘ Multiset.prod)).sum ≤
      ((s.powersetCard j).map fun _ => η ^ j).sum := by
    refine Multiset.sum_map_le_sum_map _ _ fun t ht => ?_
    obtain ⟨hts, htj⟩ := Multiset.mem_powersetCard.mp ht
    rw [Function.comp_apply, ← htj]
    exact norm_multiset_prod_le_pow hη0 fun z hz => hη z (Multiset.mem_of_le hts hz)
  refine h1.trans ?_
  rw [Multiset.map_const', Multiset.sum_replicate, Multiset.card_powersetCard, nsmul_eq_mul]
  have h2 : ((Multiset.card s).choose j : ℝ) ≤ 2 ^ Multiset.card s := by
    exact_mod_cast Nat.choose_le_two_pow _ _
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hη0 j)

/-- The coefficients of `rootPowerPolynomial p q` when the roots of `p` have modulus at most
`θ ≥ 0`. -/
theorem norm_coeff_rootPowerPolynomial_le {p : ℂ[X]} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ z ∈ p.roots, ‖z‖ ≤ θ) (q : ℕ) {k : ℕ} (hk : k ≤ p.natDegree) :
    ‖(rootPowerPolynomial p q).coeff k‖ ≤ 2 ^ p.natDegree * (θ ^ q) ^ (p.natDegree - k) := by
  have hcard : Multiset.card (p.roots.map fun z => z ^ q) = p.natDegree := by
    rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree]
  rw [rootPowerPolynomial, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hk), hcard,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h := norm_esymm_le (s := p.roots.map fun z => z ^ q) (pow_nonneg hθ0 q) ?_
    (p.natDegree - k)
  · rwa [hcard] at h
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg z) (hθ z hz) q

/-- For `0 ≤ θ < 1` there is a power `q ≥ 1` with `2^N (θ^q)^i ≤ 2^{-i}/N` for
`1 ≤ i ≤ N`. -/
theorem exists_pow_coeff_small (N : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ i : ℕ, 1 ≤ i → i ≤ N → 2 ^ N * (θ ^ q) ^ i ≤ (1 / 2) ^ i / N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact ⟨1, le_rfl, fun i hi hiN => by omega⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : (0 : ℝ) < 1 / (2 ^ (N + 1) * N) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hθ
  refine ⟨n + 1, by omega, fun i hi _ => ?_⟩
  set η : ℝ := θ ^ (n + 1) with hηdef
  have hη0 : 0 ≤ η := pow_nonneg hθ0 _
  have hηn : η ≤ θ ^ n := pow_le_pow_of_le_one hθ0 hθ.le (Nat.le_succ n)
  have hη : η < 1 / (2 ^ (N + 1) * N) := hηn.trans_lt hn
  have h2η : 2 ^ N * (2 * η) ≤ 1 / N := by
    have : 2 ^ N * (2 * η) < 2 ^ N * (2 * (1 / (2 ^ (N + 1) * N))) := by gcongr
    refine this.le.trans (le_of_eq ?_)
    field_simp
    ring
  have h2η1 : 2 * η ≤ 1 := by
    have h1 : 1 / (2 ^ (N + 1) * (N : ℝ)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (2 : ℝ) ≤ 2 ^ (N + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    linarith
  have hpow : (2 * η) ^ i ≤ 2 * η := pow_le_of_le_one (by positivity) h2η1 (by omega)
  calc 2 ^ N * η ^ i = 2 ^ N * (2 * η) ^ i * (1 / 2) ^ i := by
        rw [mul_pow, mul_assoc, mul_assoc, mul_comm (η ^ i), ← mul_assoc ((2 : ℝ) ^ i),
          ← mul_pow]
        norm_num
    _ ≤ 2 ^ N * (2 * η) * (1 / 2) ^ i := by gcongr
    _ ≤ 1 / N * (1 / 2) ^ i := by gcongr
    _ = (1 / 2) ^ i / N := by ring

end RootPower

section Recurrence

/-- **Decay of a linear recurrence with small coefficients.** If
`f (n + N) = -∑_{k < N} c_k f (n + k)` with `‖c_k‖ ≤ 2^{-(N - k)}/N`, then the bound
`‖f n‖ ≤ K 2^{-n}` (`K ≥ 0`) for `n < N` holds for all `n`. -/
theorem norm_le_of_linearRecurrence {f : ℕ → ℂ} {N : ℕ} {c : ℕ → ℂ}
    (hrec : ∀ n, f (n + N) = -∑ k ∈ Finset.range N, c k * f (n + k))
    (hc : ∀ k < N, ‖c k‖ ≤ (1 / 2) ^ (N - k) / N) {K : ℝ} (hK : 0 ≤ K)
    (h0 : ∀ n < N, ‖f n‖ ≤ K * (1 / 2) ^ n) (n : ℕ) : ‖f n‖ ≤ K * (1 / 2) ^ n := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have := hrec n
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at this
    rw [this, norm_zero]
    positivity
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with hn | hn
    · exact h0 n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
    rw [hrec m, norm_neg]
    calc ‖∑ k ∈ Finset.range N, c k * f (m + k)‖
        ≤ ∑ k ∈ Finset.range N, ‖c k‖ * ‖f (m + k)‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ ≤ ∑ k ∈ Finset.range N, (1 / 2) ^ (N - k) / N * (K * (1 / 2) ^ (m + k)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          exact mul_le_mul (hc k hk') (ih (m + k) (by omega)) (norm_nonneg _) (by positivity)
      _ = ∑ k ∈ Finset.range N, K * (1 / 2) ^ (m + N) / N := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          have e : (1 / 2 : ℝ) ^ (N - k) * (1 / 2) ^ (m + k) = (1 / 2) ^ (m + N) := by
            rw [← pow_add]
            congr 1
            omega
          rw [← e]
          ring
      _ = K * (1 / 2) ^ (m + N) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp

variable {G : Type*} [Group G]

/-- A function annihilated by `p(ρ(b))` (`ρ` the right translation, `p` monic) satisfies the
linear recurrence of `p` along the powers of `b`. -/
theorem eq_neg_sum_of_aeval_eq_zero (b : G) {p : ℂ[X]} (hp : p.Monic) {F : G → ℂ}
    (h : aeval (GroupAction.rightFunctions b) p F = 0) (m : G) (n : ℕ) :
    F (m * b ^ (n + p.natDegree)) =
      -∑ k ∈ Finset.range p.natDegree, p.coeff k * F (m * b ^ (n + k)) := by
  have hpow : ∀ (k : ℕ) (x : G),
      ((GroupAction.rightFunctions b) ^ k) F x = F (x * b ^ k) := by
    intro k x
    rw [← map_pow, GroupAction.rightFunctions_apply]
  have h1 := congrFun h (m * b ^ n)
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply] at h1
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hpow, Pi.zero_apply] at h1
  rw [Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h1
  have e : ∀ k, m * b ^ n * b ^ k = m * b ^ (n + k) := fun k => by rw [mul_assoc, pow_add]
  simp only [e] at h1
  linear_combination h1

/-- **Decay along the powers of `b`** (estimate (2) in the proof of Waldspurger's
Lemma VI.2.3). If `p(ρ(b))` kills `F` for a monic `p` of degree `N` whose coefficients satisfy
`‖c_k‖ ≤ 2^{-(N - k)}/N` for `k < N`, and `‖F(m bⁿ)‖ ≤ K 2^{-n}` for `n < N`, then this holds
for all `n`. -/
theorem norm_le_of_aeval_eq_zero (b : G) {p : ℂ[X]} (hp : p.Monic)
    (hc : ∀ k < p.natDegree, ‖p.coeff k‖ ≤ (1 / 2) ^ (p.natDegree - k) / p.natDegree)
    {F : G → ℂ} (h : aeval (GroupAction.rightFunctions b) p F = 0) (m : G) {K : ℝ}
    (hK : 0 ≤ K) (h0 : ∀ n < p.natDegree, ‖F (m * b ^ n)‖ ≤ K * (1 / 2) ^ n) (n : ℕ) :
    ‖F (m * b ^ n)‖ ≤ K * (1 / 2) ^ n :=
  norm_le_of_linearRecurrence (f := fun n => F (m * b ^ n)) (c := p.coeff)
    (fun n => eq_neg_sum_of_aeval_eq_zero b hp h m n) hc hK h0 n

end Recurrence

section Decay

/-- `(1 + x)^d ≤ (1 + 1/s)^d e^{d s x}` for `s > 0`, `x ≥ 0`. -/
theorem one_add_pow_le_mul_exp {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (d : ℕ) :
    (1 + x) ^ d ≤ (1 + 1 / s) ^ d * Real.exp (d * (s * x)) := by
  have h1 : 1 + x ≤ (1 + 1 / s) * (1 + s * x) := by
    have : (1 + 1 / s) * (1 + s * x) = 1 + x + (s * x + 1 / s) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ s * x + 1 / s := by positivity
    linarith
  have h2 : 1 + s * x ≤ Real.exp (s * x) := by
    have := Real.add_one_le_exp (s * x)
    linarith
  calc (1 + x) ^ d ≤ ((1 + 1 / s) * (1 + s * x)) ^ d :=
        pow_le_pow_left₀ (by linarith) h1 d
    _ = (1 + 1 / s) ^ d * (1 + s * x) ^ d := mul_pow _ _ _
    _ ≤ (1 + 1 / s) ^ d * Real.exp (s * x) ^ d := by
        gcongr
    _ = (1 + 1 / s) ^ d * Real.exp (d * (s * x)) := by rw [Real.exp_nat_mul]

/-- `(1/2)^n = e^{-n log 2}`. -/
theorem one_half_pow_eq_exp (n : ℕ) : (1 / 2 : ℝ) ^ n = Real.exp (-(n * Real.log 2)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div,
    inv_pow]

variable {G : Type*} [Group G] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- An additive map `H : G → E` sends `gⁿ` to `n • H(g)`. -/
theorem map_pow_of_additive {H : G → E} (hH : ∀ x y, H (x * y) = H x + H y) (g : G) (n : ℕ) :
    H (g ^ n) = (n : ℝ) • H g := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_smul]
    simpa using hH 1 1
  | succ n ih => rw [pow_succ, hH, ih, Nat.cast_succ, add_smul, one_smul]

/-- **Waldspurger, Lemma VI.2.3, abstract form.** Let `H : G → E` be additive, and let
`S₀`, `S` be finite sets of linear forms on `E` (the source's `Δ_0^{M'}` and
`Δ_0 − Δ_0^{M'}`), with `a ∈ G` such that `β(H(a)) = 0` for `β ∈ S₀` and `α(H(a)) > 0` for
`α ∈ S`. Let `σ ≥ 0` be subadditive with `1 + σ ≤ C (1 + ‖H‖)`, and `B ≥ 0` invariant under
right translation by `a`. Let `F i` be functions annihilated by `p_i(ρ(a))`, `ρ` the right
translation, for monic `p_i` of degree `N` whose roots have modulus at most `θ < 1`. Assume the
bound `‖F i g‖ ≤ C₁ B(g) (1 + σ(g))^d` on `{β(H g) ≥ 0, β ∈ S₀; α(H g) ≥ t, α ∈ S}` (`t ≥ 0`)
and the bound `‖F i g‖ ≤ C₀ B(g)` on the bounded part `‖H g‖ ≤ t/δ` of
`D(δ) = {β(H g) ≥ 0, β ∈ S₀; α(H g) ≥ δ ‖H g‖, α ∈ S}`. Then there are `ε > 0` and `C` with
`‖F i g‖ ≤ C B(g) e^{-ε ‖H g‖}` on `D(δ)`, for all `i`. -/
theorem exists_norm_le_exp_of_aeval_eq_zero {H : G → E} (hH : ∀ x y, H (x * y) = H x + H y)
    {S₀ S : Finset (Module.Dual ℝ E)} {a : G} (ha₀ : ∀ β ∈ S₀, β (H a) = 0)
    (ha : ∀ α ∈ S, 0 < α (H a)) {σ : G → ℝ} (hσ0 : ∀ g, 0 ≤ σ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (hσH : ∃ C : ℝ, ∀ g, 1 + σ g ≤ C * (1 + ‖H g‖))
    {B : G → ℝ} (hB0 : ∀ g, 0 ≤ B g) (hB : ∀ g, B (g * a) = B g)
    {ι : Type*} {F : ι → G → ℂ} {p : ι → ℂ[X]} {N : ℕ} {θ : ℝ} (hθ : θ < 1)
    (hp : ∀ i, (p i).Monic) (hpN : ∀ i, (p i).natDegree = N)
    (hroots : ∀ i, ∀ z ∈ (p i).roots, ‖z‖ ≤ θ)
    (hann : ∀ i, aeval (GroupAction.rightFunctions a) (p i) (F i) = 0)
    {t : ℝ} (ht : 0 ≤ t) {C₁ : ℝ} {d : ℕ}
    (h1 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) →
      ‖F i g‖ ≤ C₁ * B g * (1 + σ g) ^ d)
    {δ : ℝ} (hδ : 0 < δ) {C₀ : ℝ}
    (h0 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
      ‖H g‖ ≤ t / δ → ‖F i g‖ ≤ C₀ * B g) :
    ∃ ε > 0, ∃ C : ℝ, ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
      ‖F i g‖ ≤ C * B g * Real.exp (-(ε * ‖H g‖)) := by
  classical
  -- the power `q` making the coefficients small
  set θ' : ℝ := max θ 0 with hθ'
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'1 : θ' < 1 := max_lt hθ (by norm_num)
  have hroots' : ∀ i, ∀ z ∈ (p i).roots, ‖z‖ ≤ θ' := fun i z hz =>
    (hroots i z hz).trans (le_max_left _ _)
  obtain ⟨q, hq1, hqsmall⟩ := exists_pow_coeff_small N hθ'0 hθ'1
  set b : G := a ^ q with hb
  have hp'm : ∀ i, (rootPowerPolynomial (p i) q).Monic := fun i => rootPowerPolynomial_monic _ _
  have hp'N : ∀ i, (rootPowerPolynomial (p i) q).natDegree = N := fun i => by
    rw [natDegree_rootPowerPolynomial, hpN]
  have hann' : ∀ i,
      aeval (GroupAction.rightFunctions b) (rootPowerPolynomial (p i) q) (F i) = 0 := by
    intro i
    rw [hb, map_pow]
    exact aeval_rootPowerPolynomial_eq_zero _ (hp i) q (hann i)
  have hc' : ∀ i, ∀ k < (rootPowerPolynomial (p i) q).natDegree,
      ‖(rootPowerPolynomial (p i) q).coeff k‖ ≤
        (1 / 2) ^ ((rootPowerPolynomial (p i) q).natDegree - k) /
          (rootPowerPolynomial (p i) q).natDegree := by
    intro i k hk
    rw [hp'N i] at hk ⊢
    have h := norm_coeff_rootPowerPolynomial_le hθ'0 (hroots' i) q (k := k)
      (by rw [hpN i]; exact hk.le)
    rw [hpN i] at h
    exact h.trans (hqsmall (N - k) (by omega) (by omega))
  -- facts on `H`, `B` and `b`
  have hHpow : ∀ (g : G) (n : ℕ), H (g ^ n) = (n : ℝ) • H g := map_pow_of_additive hH
  have hbS₀ : ∀ β ∈ S₀, β (H b) = 0 := fun β hβ => by
    rw [hb, hHpow, map_smul, ha₀ β hβ, smul_zero]
  have hbS : ∀ α ∈ S, 0 < α (H b) := fun α hα => by
    rw [hb, hHpow, map_smul, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hq1) (ha α hα)
  have hBa : ∀ (g : G) (n : ℕ), B (g * a ^ n) = B g := by
    intro g n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, hB, ih]
  have hBb : ∀ (g : G) (n : ℕ), B (g * b ^ n) = B g := fun g n => by
    rw [hb, ← pow_mul, hBa]
  -- estimate (2): decay along the powers of `b` on the shifted chamber
  set C₅ : ℝ := |C₁| * ∑ k ∈ Finset.range N, 2 ^ k * (1 + σ (b ^ k)) ^ d with hC₅
  have hC₅0 : 0 ≤ C₅ := mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ =>
    mul_nonneg (by positivity) (pow_nonneg (by linarith [hσ0 (b ^ k)]) _))
  have hstep : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) → ∀ n : ℕ,
      ‖F i (g * b ^ n)‖ ≤ C₅ * B g * (1 + σ g) ^ d * (1 / 2) ^ n := by
    intro i g hg0 hgt n
    have hσg : 0 ≤ 1 + σ g := by linarith [hσ0 g]
    have hK : 0 ≤ C₅ * B g * (1 + σ g) ^ d :=
      mul_nonneg (mul_nonneg hC₅0 (hB0 g)) (pow_nonneg hσg d)
    refine norm_le_of_aeval_eq_zero b (hp'm i) (hc' i) (hann' i) g hK (fun n hn => ?_) n
    rw [hp'N i] at hn
    have hgn0 : ∀ β ∈ S₀, 0 ≤ β (H (g * b ^ n)) := by
      intro β hβ
      rw [hH, hHpow, map_add, map_smul, hbS₀ β hβ, smul_zero, add_zero]
      exact hg0 β hβ
    have hgnt : ∀ α ∈ S, t ≤ α (H (g * b ^ n)) := by
      intro α hα
      rw [hH, hHpow, map_add, map_smul, smul_eq_mul]
      linarith [hgt α hα, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (hbS α hα).le]
    have h1' := h1 i (g * b ^ n) hgn0 hgnt
    rw [hBb] at h1'
    have hσmul : 1 + σ (g * b ^ n) ≤ (1 + σ g) * (1 + σ (b ^ n)) := by
      nlinarith [hσ g (b ^ n), hσ0 g, hσ0 (b ^ n), mul_nonneg (hσ0 g) (hσ0 (b ^ n))]
    have hterm : 2 ^ n * (1 + σ (b ^ n)) ^ d ≤
        ∑ k ∈ Finset.range N, 2 ^ k * (1 + σ (b ^ k)) ^ d :=
      Finset.single_le_sum (f := fun k => (2 : ℝ) ^ k * (1 + σ (b ^ k)) ^ d)
        (fun k _ => mul_nonneg (by positivity) (pow_nonneg (by linarith [hσ0 (b ^ k)]) _))
        (Finset.mem_range.mpr hn)
    have hσgn : 0 ≤ 1 + σ (g * b ^ n) := by linarith [hσ0 (g * b ^ n)]
    have hσbn : 0 ≤ 1 + σ (b ^ n) := by linarith [hσ0 (b ^ n)]
    calc ‖F i (g * b ^ n)‖ ≤ C₁ * B g * (1 + σ (g * b ^ n)) ^ d := h1'
      _ ≤ |C₁| * B g * ((1 + σ g) * (1 + σ (b ^ n))) ^ d := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C₁) (hB0 g))
            (pow_le_pow_left₀ hσgn hσmul d) (pow_nonneg hσgn d)
            (mul_nonneg (abs_nonneg _) (hB0 g))
      _ = |C₁| * B g * (1 + σ g) ^ d * (2 ^ n * (1 + σ (b ^ n)) ^ d) * (1 / 2) ^ n := by
          rw [mul_pow]
          have e : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
          linear_combination (|C₁| * B g * (1 + σ g) ^ d * (1 + σ (b ^ n)) ^ d) * e.symm
      _ ≤ |C₁| * B g * (1 + σ g) ^ d *
            (∑ k ∈ Finset.range N, 2 ^ k * (1 + σ (b ^ k)) ^ d) * (1 / 2) ^ n := by
          gcongr
          exact mul_nonneg (mul_nonneg (abs_nonneg _) (hB0 g)) (pow_nonneg hσg d)
      _ = C₅ * B g * (1 + σ g) ^ d * (1 / 2) ^ n := by rw [hC₅]; ring
  -- constants for the final estimate
  obtain ⟨Cσ, hCσ⟩ := hσH
  set c : ℝ := ∑ α ∈ S, α (H b) + 1 with hc
  have hsum0 : 0 ≤ ∑ α ∈ S, α (H b) := Finset.sum_nonneg fun α hα => (hbS α hα).le
  have hcpos : 0 < c := by linarith
  have hαc : ∀ α ∈ S, α (H b) ≤ c := fun α hα => by
    have := Finset.single_le_sum (f := fun β => β (H b)) (fun β hβ => (hbS β hβ).le) hα
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set r : ℝ := δ * Real.log 2 / c with hr
  have hrpos : 0 < r := by positivity
  set ε : ℝ := r / 2 with hε
  have hεpos : 0 < ε := by positivity
  set s : ℝ := ε / (d + 1) with hs
  have hspos : 0 < s := by positivity
  have hds : (d : ℝ) * s ≤ ε := by
    rw [hs, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set C₆ : ℝ := |Cσ| * (1 + δ * ‖H b‖ / c) with hC₆
  set Cbig : ℝ := C₅ * C₆ ^ d * (1 + 1 / s) ^ d * Real.exp ((t / c + 1) * Real.log 2)
    with hCbig
  set Csmall : ℝ := |C₀| * Real.exp (ε * (t / δ)) with hCsmall
  refine ⟨ε, hεpos, max Cbig Csmall, fun i g hg0 hgδ => ?_⟩
  set x : ℝ := ‖H g‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hexp0 : 0 ≤ Real.exp (-(ε * x)) := (Real.exp_pos _).le
  rcases le_or_gt x (t / δ) with hsmall | hlarge
  · -- the bounded part
    have h := h0 i g hg0 hgδ hsmall
    have he : 1 ≤ Real.exp (ε * (t / δ)) * Real.exp (-(ε * x)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    calc ‖F i g‖ ≤ C₀ * B g := h
      _ ≤ |C₀| * B g := mul_le_mul_of_nonneg_right (le_abs_self C₀) (hB0 g)
      _ ≤ |C₀| * B g * (Real.exp (ε * (t / δ)) * Real.exp (-(ε * x))) :=
          le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (hB0 g)) he
      _ = Csmall * B g * Real.exp (-(ε * x)) := by rw [hCsmall]; ring
      _ ≤ max Cbig Csmall * B g * Real.exp (-(ε * x)) := by
          gcongr
          · exact hB0 g
          · exact le_max_right _ _
  · -- the far part: translate back into the shifted chamber
    have hδx : t < δ * x := by rwa [div_lt_iff₀ hδ, mul_comm] at hlarge
    set n : ℕ := ⌊(δ * x - t) / c⌋₊ with hn
    set g' : G := g * (b ^ n)⁻¹ with hg'
    have hgg' : g' * b ^ n = g := by rw [hg', inv_mul_cancel_right]
    have hHg' : H g = H g' + (n : ℝ) • H b := by
      conv_lhs => rw [← hgg']
      rw [hH, hHpow]
    have hnc : (n : ℝ) * c ≤ δ * x - t := by
      have := Nat.floor_le (div_nonneg (sub_nonneg.mpr hδx.le) hcpos.le)
      rwa [← hn, le_div_iff₀ hcpos] at this
    have hnlb : (δ * x - t) / c - 1 < n := by
      have := Nat.lt_floor_add_one ((δ * x - t) / c)
      rw [← hn] at this
      linarith
    have hg'0 : ∀ β ∈ S₀, 0 ≤ β (H g') := by
      intro β hβ
      have := hg0 β hβ
      rwa [hHg', map_add, map_smul, hbS₀ β hβ, smul_zero, add_zero] at this
    have hg't : ∀ α ∈ S, t ≤ α (H g') := by
      intro α hα
      have h1 := hgδ α hα
      rw [hHg', map_add, map_smul, smul_eq_mul] at h1
      have h2 : (n : ℝ) * α (H b) ≤ n * c :=
        mul_le_mul_of_nonneg_left (hαc α hα) (Nat.cast_nonneg n)
      linarith
    have hmain := hstep i g' hg'0 hg't n
    have hBg' : B g' = B g := by rw [← hBb g' n, hgg']
    rw [hgg', hBg'] at hmain
    -- the factor `1 + σ(g')`
    have hσg' : 1 + σ g' ≤ C₆ * (1 + x) := by
      have hn_le : (n : ℝ) ≤ δ * x / c := by
        rw [le_div_iff₀ hcpos]
        linarith
      have hHg'n : ‖H g'‖ ≤ x + δ * x / c * ‖H b‖ := by
        have e : H g' = H g - (n : ℝ) • H b := by rw [hHg']; abel
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_natCast]
        gcongr
      have hk0 : 0 ≤ δ * ‖H b‖ / c := by positivity
      calc 1 + σ g' ≤ Cσ * (1 + ‖H g'‖) := hCσ g'
        _ ≤ |Cσ| * (1 + ‖H g'‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self Cσ) (by positivity)
        _ ≤ |Cσ| * ((1 + δ * ‖H b‖ / c) * (1 + x)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have : δ * x / c * ‖H b‖ = δ * ‖H b‖ / c * x := by ring
            nlinarith
        _ = C₆ * (1 + x) := by rw [hC₆]; ring
    -- the factor `2^{-n}`
    have hhalf : (1 / 2 : ℝ) ^ n ≤
        Real.exp ((t / c + 1) * Real.log 2) * Real.exp (-(r * x)) := by
      rw [one_half_pow_eq_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e : (t / c + 1) * Real.log 2 + -(r * x) =
          -(((δ * x - t) / c - 1) * Real.log 2) := by
        rw [hr]
        field_simp
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hnlb.le hlog.le
      linarith
    have hpoly := one_add_pow_le_mul_exp hspos hx0 d
    have hσg'0 : 0 ≤ 1 + σ g' := by linarith [hσ0 g']
    have hC₆0 : 0 ≤ C₆ := by positivity
    have hexp_comb : Real.exp (d * (s * x)) * Real.exp (-(r * x)) ≤ Real.exp (-(ε * x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : (d : ℝ) * (s * x) ≤ ε * x := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hds hx0
      have hr2 : r = 2 * ε := by rw [hε]; ring
      rw [hr2]
      linarith only [this]
    have hB := hB0 g
    have hCB : 0 ≤ C₅ * B g := mul_nonneg hC₅0 hB
    have hx1 : 0 ≤ 1 + x := by linarith
    have hE1 : 0 ≤ Real.exp ((t / c + 1) * Real.log 2) * Real.exp (-(r * x)) :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hCbig0 : 0 ≤ Cbig :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₅0 (pow_nonneg hC₆0 d))
        (pow_nonneg (by positivity) d)) (Real.exp_pos _).le
    calc ‖F i g‖ ≤ C₅ * B g * (1 + σ g') ^ d * (1 / 2) ^ n := hmain
      _ ≤ C₅ * B g * (C₆ * (1 + x)) ^ d *
            (Real.exp ((t / c + 1) * Real.log 2) * Real.exp (-(r * x))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσg'0 hσg' d) hCB) hhalf
            (pow_nonneg (by norm_num) n)
            (mul_nonneg hCB (pow_nonneg (mul_nonneg hC₆0 hx1) d))
      _ = C₅ * B g * C₆ ^ d * (1 + x) ^ d *
            (Real.exp ((t / c + 1) * Real.log 2) * Real.exp (-(r * x))) := by
          rw [mul_pow]
          ring
      _ ≤ C₅ * B g * C₆ ^ d * ((1 + 1 / s) ^ d * Real.exp (d * (s * x))) *
            (Real.exp ((t / c + 1) * Real.log 2) * Real.exp (-(r * x))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (mul_nonneg hCB (pow_nonneg hC₆0 d))) hE1
      _ = Cbig * B g * (Real.exp (d * (s * x)) * Real.exp (-(r * x))) := by
          rw [hCbig]
          ring
      _ ≤ Cbig * B g * Real.exp (-(ε * x)) :=
          mul_le_mul_of_nonneg_left hexp_comb (mul_nonneg hCbig0 hB)
      _ ≤ max Cbig Csmall * B g * Real.exp (-(ε * x)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hB) hexp0

end Decay

end Langlands.HarishChandraSchwartz
