import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Lucas

/-! # Symmetric polynomial two-cocycles of the additive group -/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.Unipotent.OneDimensional

variable {k : Type*} [Field k]

section Eval

variable {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation of a two-variable polynomial `c = ∑ cⱼ(X) Yʲ ∈ k[X][Y]` at `(u, v)`. -/
def ev2 (u v : R) : k[X][X] →ₐ[k] R :=
  eval₂AlgHom (aeval u) v fun _ => Commute.all _ _

theorem ev2_apply (u v : R) (c : k[X][X]) :
    ev2 u v c = c.eval₂ (aeval u : k[X] →ₐ[k] R).toRingHom v :=
  rfl

@[simp] theorem ev2_C (u v : R) (a : k[X]) : ev2 u v (C a) = aeval u a := by
  simp [ev2_apply]

@[simp] theorem ev2_X (u v : R) : ev2 u v (X : k[X][X]) = v := by
  simp [ev2_apply]

@[simp] theorem ev2_C_X (u v : R) : ev2 u v (C X : k[X][X]) = u := by
  simp [ev2_apply]

theorem ev2_aeval (u v : R) (q : k[X][X]) (f : k[X]) :
    ev2 u v (aeval q f) = aeval (ev2 u v q) f :=
  (aeval_algHom_apply (ev2 u v) q f).symm

theorem comp_ev2 {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (u v : R)
    (c : k[X][X]) : φ (ev2 u v c) = ev2 (φ u) (φ v) c := by
  have h : φ.comp (ev2 u v) = ev2 (φ u) (φ v) := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp
    · simp
  exact AlgHom.congr_fun h c

end Eval

/-- The two-variable polynomial `h(X + Y)` for `h ∈ k[X]`. -/
abbrev shift (h : k[X]) : k[X][X] := aeval (C X + X) h

/-- The coboundary `f(X + Y) - f(X) - f(Y)` of a one-variable polynomial. -/
def coboundary (f : k[X]) : k[X][X] :=
  aeval (C X + X : k[X][X]) f - aeval (C X : k[X][X]) f - aeval (X : k[X][X]) f

theorem ev2_coboundary {R : Type*} [CommRing R] [Algebra k R] (u v : R) (f : k[X]) :
    ev2 u v (coboundary f) = aeval (u + v) f - aeval u f - aeval v f := by
  simp [coboundary, ev2_aeval]

/-- The three coordinate variables of `k[X][Y][Z]`. -/
abbrev varU : k[X][X][X] := C (C X)
abbrev varV : k[X][X][X] := C X
abbrev varW : k[X][X][X] := X

/-- The defect `c(X+Y, Z) + c(X, Y) - c(X, Y+Z) - c(Y, Z)` of the two-cocycle identity. -/
def defect (c : k[X][X]) : k[X][X][X] :=
  ev2 (varU (k := k) + varV) varW c + ev2 (varU (k := k)) varV c -
    ev2 (varU (k := k)) (varV + varW) c - ev2 (varV (k := k)) varW c

/-- The two-cocycle identity `c(X+Y, Z) + c(X, Y) = c(X, Y+Z) + c(Y, Z)` in `k[X][Y][Z]`. -/
def IsCocycle (c : k[X][X]) : Prop :=
  defect c = 0

/-- The `p`-power obstruction `∑_{i < p} c(i X, X)`. -/
def powerSum (p : ℕ) (c : k[X][X]) : k[X] :=
  ∑ i ∈ Finset.range p, ev2 ((i : k[X]) * X) X c

section Forms

theorem ev2_C_X_eq_map (a : k[X][X]) (c : k[X][X]) :
    ev2 (C a : k[X][X][X]) X c = c.map (aeval a).toRingHom := by
  rw [ev2_apply, Polynomial.map]
  congr 1
  ext : 1
  · ext x
    simp [aeval_C]
  · simp

theorem ev2_U_V (c : k[X][X]) : ev2 varU varV c = C c := by
  have h : (ev2 varU varV : k[X][X] →ₐ[k] k[X][X][X]) = (CAlgHom : k[X][X] →ₐ[k] _) := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp
    · simp
  exact AlgHom.congr_fun h c

theorem ev2_U_VW (c : k[X][X]) :
    ev2 varU (varV + varW) c = taylor (X : k[X][X]) (c.map C) := by
  rw [taylor_apply, comp, eval₂_map, ev2_apply]
  congr 1
  · ext : 1
    · ext x
      simp [aeval_C]
    · simp
  · simp [add_comm]

theorem ev2_UV_W (c : k[X][X]) :
    ev2 (varU (k := k) + varV) varW c = c.map (aeval (C X + X : k[X][X])).toRingHom := by
  rw [show varU (k := k) + varV = C (C X + X) from C_add.symm]
  exact ev2_C_X_eq_map _ c

theorem ev2_V_W (c : k[X][X]) :
    ev2 (varV (k := k)) varW c = c.map (aeval (X : k[X][X])).toRingHom :=
  ev2_C_X_eq_map X c

end Forms

section Shift

theorem shift_eq_taylor (h : k[X]) : shift h = taylor (X : k[X]) (h.map C) := by
  rw [taylor_apply, comp, eval₂_map, shift, aeval_def, add_comm]
  rfl

theorem coeff_shift (h : k[X]) (n : ℕ) : (shift h).coeff n = hasseDeriv n h := by
  rw [shift_eq_taylor, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

theorem coeff_aeval_X (h : k[X]) (n : ℕ) :
    (aeval (X : k[X][X]) h).coeff n = C (h.coeff n) := by
  simp [aeval_X_left_eq_map, coeff_map]

theorem aeval_C_X (f : k[X]) : aeval (C X : k[X][X]) f = C f := by
  have h : (aeval (C X : k[X][X]) : k[X] →ₐ[k] k[X][X]) = (CAlgHom : k[X] →ₐ[k] k[X][X]) := by
    apply Polynomial.algHom_ext
    simp
  simpa using AlgHom.congr_fun h f

theorem derivative_shift (h : k[X]) : derivative (shift h) = shift (derivative h) := by
  rw [shift_eq_taylor, shift_eq_taylor, taylor_apply, taylor_apply, derivative_comp,
    derivative_add, derivative_X, derivative_C, add_zero, one_mul, derivative_map]

theorem derivative_aeval_X (h : k[X]) :
    derivative (aeval (X : k[X][X]) h) = aeval (X : k[X][X]) (derivative h) := by
  rw [aeval_X_left_eq_map, aeval_X_left_eq_map, derivative_map]

end Shift

section Coboundary

@[simp] theorem coboundary_zero : coboundary (0 : k[X]) = 0 := by
  simp [coboundary]

theorem coboundary_add (f g : k[X]) : coboundary (f + g) = coboundary f + coboundary g := by
  simp only [coboundary, map_add]
  ring

theorem coeff_coboundary (f : k[X]) (n : ℕ) :
    (coboundary f).coeff n = hasseDeriv n f - (C f).coeff n - C (f.coeff n) := by
  rw [coboundary, coeff_sub, coeff_sub, coeff_shift, aeval_C_X, coeff_aeval_X]

theorem coeff_zero_coboundary (f : k[X]) : (coboundary f).coeff 0 = -C (f.coeff 0) := by
  rw [coeff_coboundary, hasseDeriv_zero', coeff_C_zero, sub_self, zero_sub]

theorem derivative_coboundary (f : k[X]) :
    derivative (coboundary f) = shift (derivative f) - aeval X (derivative f) := by
  rw [coboundary, derivative_sub, derivative_sub, derivative_shift, aeval_C_X, derivative_C,
    sub_zero, derivative_aeval_X]

theorem natDegree_coboundary_le (f : k[X]) : (coboundary f).natDegree ≤ f.natDegree - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn1 : n ≠ 0 := by omega
  rw [coeff_coboundary, coeff_C, ite_eq_right hn1, sub_zero]
  rcases Nat.lt_or_ge f.natDegree n with h | h
  · rw [hasseDeriv_eq_zero_of_lt_natDegree f n h, coeff_eq_zero_of_natDegree_lt h, C_0, sub_zero]
  · have : n = f.natDegree := by omega
    subst this
    rw [hasseDeriv_natDegree_eq_C, coeff_natDegree, sub_self]

theorem swap_coboundary (f : k[X]) : Bivariate.swap (coboundary f) = coboundary f := by
  have key : ∀ q : k[X][X], Bivariate.swap (aeval q f) = aeval (Bivariate.swap q) f :=
    fun q => (aeval_algHom_apply (Bivariate.swap : k[X][X] ≃ₐ[k] k[X][X]).toAlgHom q f).symm
  simp only [coboundary, map_sub, key, map_add, Bivariate.swap_X, Bivariate.swap_Y]
  rw [add_comm (X : k[X][X])]
  abel

theorem defect_sub (c d : k[X][X]) : defect (c - d) = defect c - defect d := by
  simp only [defect, map_sub]
  ring

theorem IsCocycle.sub {c d : k[X][X]} (hc : IsCocycle c) (hd : IsCocycle d) :
    IsCocycle (c - d) := by
  have h1 : defect c = 0 := hc
  have h2 : defect d = 0 := hd
  show defect (c - d) = 0
  rw [defect_sub, h1, h2]
  exact sub_zero (0 : k[X][X][X])

theorem isCocycle_coboundary (f : k[X]) : IsCocycle (coboundary f) := by
  have h : varU (k := k) + varV + varW = varU + (varV + varW) := add_assoc _ _ _
  simp only [IsCocycle, defect, ev2_coboundary, h]
  ring

end Coboundary

section Swap

theorem coeff_coeff_monomial_monomial (i j n m : ℕ) (r : k) :
    ((monomial i (monomial j r) : k[X][X]).coeff n).coeff m = if i = n ∧ j = m then r else 0 := by
  by_cases h1 : i = n <;> by_cases h2 : j = m <;> simp [coeff_monomial, h1, h2]

theorem coeff_coeff_swap (c : k[X][X]) (m n : ℕ) :
    ((Bivariate.swap c).coeff n).coeff m = (c.coeff m).coeff n := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial i a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, coeff_add, ha, hb]
    | monomial j r =>
      rw [Bivariate.swap_monomial_monomial, coeff_coeff_monomial_monomial,
        coeff_coeff_monomial_monomial]
      by_cases h1 : j = n <;> by_cases h2 : i = m <;> simp [h1, h2]

end Swap

section Derivative

theorem derivative_eq_of_isCocycle {c : k[X][X]} (hc : IsCocycle c) :
    derivative c = shift (c.coeff 1) - aeval X (c.coeff 1) := by
  have h := congrArg (fun q : k[X][X][X] => q.coeff 1) (show defect c = 0 from hc)
  simp only [defect, coeff_add, coeff_sub, ev2_UV_W, ev2_U_V, ev2_U_VW, ev2_V_W, coeff_map,
    coeff_C, one_ne_zero, ite_false, taylor_coeff_one, derivative_map, eval_map, eval₂_C_X,
    coeff_zero] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  linear_combination -h

end Derivative

section PowerSum

theorem powerSum_sub (p : ℕ) (c d : k[X][X]) :
    powerSum p (c - d) = powerSum p c - powerSum p d := by
  simp [powerSum, Finset.sum_sub_distrib]

theorem powerSum_coboundary (p : ℕ) [CharP k p] (f : k[X]) : powerSum p (coboundary f) = 0 := by
  have h1 : ∀ i : ℕ, aeval ((i : k[X]) * X + X) f - aeval ((i : k[X]) * X) f - aeval X f =
      (aeval (((i + 1 : ℕ) : k[X]) * X) f - aeval ((i : k[X]) * X) f) - aeval X f := by
    intro i
    rw [Nat.cast_succ, add_mul, one_mul]
  simp only [powerSum, ev2_coboundary, h1]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => aeval ((i : k[X]) * X) f)]
  simp

theorem powerSum_pow (p : ℕ) [Fact p.Prime] [CharP k p] (c : k[X][X]) :
    powerSum p (c ^ p) = powerSum p c ^ p := by
  simp only [powerSum, map_pow]
  rw [sum_pow_char]

theorem coeff_ev2_C_mul_X (a : k) (c : k[X][X]) (N : ℕ) :
    (ev2 (C a * X) (X : k[X]) c).coeff N =
      ∑ x ∈ Finset.antidiagonal N, a ^ x.1 * (c.coeff x.2).coeff x.1 := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | monomial i q =>
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => simp only [map_add, coeff_add, h₁, h₂, mul_add, Finset.sum_add_distrib]
    | monomial j r =>
      have hev : ev2 (C a * X) (X : k[X]) (monomial i (monomial j r)) =
          C (r * a ^ j) * X ^ (j + i) := by
        rw [ev2_apply, eval₂_monomial]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_monomial, algebraMap_eq,
          mul_pow, ← C_pow, pow_add, C_mul]
        ring
      rw [hev, coeff_C_mul_X_pow]
      simp_rw [coeff_coeff_monomial_monomial, mul_ite, mul_zero]
      by_cases hN : N = j + i
      · rw [ite_eq_left hN, Finset.sum_eq_single (j, i)]
        · simp [mul_comm]
        · rintro ⟨b1, b2⟩ _ hb
          rw [ite_eq_right]
          rintro ⟨rfl, rfl⟩
          exact hb rfl
        · intro h
          exact absurd (Finset.mem_antidiagonal.mpr hN.symm) h
      · rw [ite_eq_right hN]
        symm
        refine Finset.sum_eq_zero fun b hb => ?_
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        apply hN
        rw [← (Finset.mem_antidiagonal.mp hb), ← h1, ← h2]

theorem sum_range_natCast_pow (p : ℕ) [Fact p.Prime] [CharP k p] (m : ℕ) :
    ∑ i ∈ Finset.range p, (i : k) ^ m = ZMod.castHom (dvd_refl p) k (∑ x : ZMod p, x ^ m) := by
  rw [map_sum]
  symm
  refine Finset.sum_nbij' (fun x => x.val) (fun i => (i : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simpa using ZMod.val_lt x
  · intro i _
    simp
  · intro x _
    simp
  · intro i hi
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · intro x _
    simp [ZMod.natCast_val]

theorem sum_range_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {m : ℕ} (hm : m < p - 1) :
    ∑ i ∈ Finset.range p, (i : k) ^ m = 0 := by
  rw [sum_range_natCast_pow, FiniteField.sum_pow_lt_card_sub_one (ZMod p) m (by rwa [ZMod.card]),
    map_zero]

theorem sum_range_pow_sub_one (p : ℕ) [hp : Fact p.Prime] [CharP k p] :
    ∑ i ∈ Finset.range p, (i : k) ^ (p - 1) = -1 := by
  have hz : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
    have h : ∀ x : ZMod p, x ^ (p - 1) = 1 - if x = 0 then 1 else 0 := by
      intro x
      split_ifs with hx
      · rw [hx, zero_pow (by have := hp.out.two_le; omega), sub_self]
      · rw [ZMod.pow_card_sub_one_eq_one hx, sub_zero]
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul, mul_one, CharP.cast_eq_zero,
      zero_sub]
  rw [sum_range_natCast_pow, hz, map_neg, map_one]

theorem coeff_powerSum (p : ℕ) [hp : Fact p.Prime] [CharP k p] {c : k[X][X]}
    (h0 : c.coeff 0 = 0) : (powerSum p c).coeff p = -(c.coeff 1).coeff (p - 1) := by
  have h2 := hp.out.two_le
  have hcast : ∀ i : ℕ, ((i : k[X]) * X) = C (i : k) * X := fun i => by rw [map_natCast]
  simp only [powerSum, finsetSum_coeff, hcast, coeff_ev2_C_mul_X]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_eq_single (p - 1, 1)]
  · rw [sum_range_pow_sub_one]
    ring
  · rintro ⟨m, n⟩ hmn hne
    rw [Finset.mem_antidiagonal] at hmn
    simp only [ne_eq, Prod.mk.injEq] at hne
    rcases Nat.lt_or_ge m (p - 1) with hm | hm
    · rw [sum_range_pow_eq_zero p hm, zero_mul]
    · have hn : n = 0 := by omega
      subst hn
      simp [h0]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp; omega)) h

end PowerSum

section Antiderivative

theorem exists_antiderivative (g : k[X]) (hg : ∀ n : ℕ, (n : k) + 1 = 0 → g.coeff n = 0) :
    ∃ G : k[X], derivative G = g ∧ G.coeff 0 = 0 ∧ G.natDegree ≤ g.natDegree + 1 := by
  refine ⟨∑ n ∈ Finset.range (g.natDegree + 1), C (g.coeff n / ((n : k) + 1)) * X ^ (n + 1),
    ?_, ?_, ?_⟩
  · rw [derivative_sum]
    conv_rhs => rw [g.as_sum_range_C_mul_X_pow]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [derivative_C_mul_X_pow]
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    congr 1
    by_cases h : (n : k) + 1 = 0
    · rw [hg n h, zero_div, zero_mul]
    · rw [div_mul_cancel₀ _ h]
  · simp [finsetSum_coeff]
  · refine natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.mp hn
    omega

end Antiderivative

section Root

theorem exists_pow_eq_of_coeff {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (f : R[X]) (hdvd : ∀ n, ¬ p ∣ n → f.coeff n = 0) (hroot : ∀ n, ∃ b : R, b ^ p = f.coeff n) :
    ∃ g : R[X], g ^ p = f := by
  choose b hb using hroot
  refine ⟨∑ n ∈ Finset.range (f.natDegree + 1), C (b n) * X ^ (n / p), ?_⟩
  rw [sum_pow_char]
  conv_rhs => rw [f.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow, ← C_pow, hb, ← pow_mul]
  by_cases h : p ∣ n
  · rw [Nat.div_mul_cancel h]
  · rw [hdvd n h, C_0, zero_mul, zero_mul]

end Root

section Main

theorem pow_add_sub_sub {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a b c d : R) : a ^ p + b ^ p - c ^ p - d ^ p = (a + b - c - d) ^ p := by
  rw [sub_pow_char, sub_pow_char, add_pow_char]

theorem defect_pow (p : ℕ) [Fact p.Prime] [CharP k p] (c : k[X][X]) :
    defect (c ^ p) = defect c ^ p := by
  simp only [defect, map_pow]
  exact pow_add_sub_sub (R := k[X][X][X]) p _ _ _ _

theorem coboundary_pow (p : ℕ) [Fact p.Prime] [CharP k p] (f : k[X]) :
    coboundary (f ^ p) = coboundary f ^ p := by
  simp only [coboundary, map_pow]
  rw [sub_pow_char, sub_pow_char]

/-- **Characteristic zero.** A normalized polynomial two-cocycle is a coboundary. -/
theorem exists_eq_coboundary_of_charZero [CharZero k] {c : k[X][X]} (hc : IsCocycle c)
    (h0 : c.coeff 0 = 0) : ∃ f : k[X], c = coboundary f := by
  obtain ⟨G, hG, hG0, -⟩ := exists_antiderivative (c.coeff 1) fun n hn =>
    absurd hn (Nat.cast_add_one_ne_zero n)
  refine ⟨G, ?_⟩
  have hD : derivative (c - coboundary G) = 0 := by
    rw [derivative_sub, derivative_eq_of_isCocycle hc, derivative_coboundary, hG, sub_self]
  have h1 := derivative_eq_zero.mp hD
  rw [← sub_eq_zero, eq_C_of_natDegree_eq_zero h1, coeff_sub, h0, coeff_zero_coboundary, hG0,
    C_0, neg_zero, sub_zero, C_0]

/-- **Characteristic `p`, perfect field.** A symmetric normalized polynomial two-cocycle with
vanishing `p`-power obstruction is a coboundary. -/
theorem exists_eq_coboundary_of_charP (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p] :
    ∀ (N : ℕ) (c : k[X][X]), c.natDegree ≤ N → IsCocycle c → Bivariate.swap c = c →
      c.coeff 0 = 0 → powerSum p c = 0 → ∃ f : k[X], c = coboundary f := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hN hc hs h0 hφ
  have h2 := hp.out.two_le
  have hsym : ∀ m n, (c.coeff n).coeff m = (c.coeff m).coeff n := fun m n => by
    have := coeff_coeff_swap c m n
    rwa [hs] at this
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · refine ⟨0, ?_⟩
    rw [coboundary_zero, eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hN), h0, C_0]
  set g := c.coeff 1 with hg_def
  have hD := derivative_eq_of_isCocycle hc
  have hγ : g.coeff (p - 1) = 0 := by
    have := coeff_powerSum p h0
    rw [hφ, coeff_zero] at this
    exact neg_eq_zero.mp this.symm
  have hgvan : ∀ n : ℕ, (n : k) + 1 = 0 → g.coeff n = 0 := by
    intro n hn
    have hpn : p ∣ n + 1 :=
      (CharP.cast_eq_zero_iff k p (n + 1)).mp (by rw [Nat.cast_succ]; exact hn)
    obtain ⟨t, ht⟩ := hpn
    rcases t with _ | t
    · omega
    have hnt : n = (p - 1) + p * t := by
      rw [Nat.mul_succ] at ht
      omega
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [show n = p - 1 by omega]
      exact hγ
    have h1 : (derivative c).coeff (p - 1) = 0 := by
      rw [coeff_derivative]
      have : ((p - 1 : ℕ) : k[X]) + 1 = 0 := by
        rw [← Nat.cast_add_one, Nat.sub_add_cancel hp.out.one_le, CharP.cast_eq_zero]
      rw [this, mul_zero]
    rw [hD, coeff_sub, coeff_shift, coeff_aeval_X] at h1
    have h3 := congrArg (fun q : k[X] => q.coeff (n - (p - 1))) h1
    simp only [coeff_sub, hasseDeriv_coeff, coeff_C, coeff_zero] at h3
    have hnp : p ≤ n := by
      have := Nat.le_mul_of_pos_right p htpos
      omega
    rw [ite_eq_right (by omega), sub_zero, Nat.sub_add_cancel (by omega)] at h3
    have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := p - 1) (p := p)
    have hmod : n % p = p - 1 := by
      rw [hnt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show p - 1 < p by omega)]
    rw [hmod, Nat.mod_eq_of_lt (show p - 1 < p by omega), Nat.div_eq_of_lt (show p - 1 < p by omega),
      Nat.choose_self,
      Nat.choose_zero_right, mul_one] at hL
    have hchoose : ((n.choose (p - 1) : ℕ) : k) = 1 := by
      rw [CharP.natCast_eq_natCast' (R := k) (p := p) hL, Nat.cast_one]
    rwa [hchoose, one_mul] at h3
  obtain ⟨G, hG, hG0, hGdeg⟩ := exists_antiderivative g hgvan
  set c1 := c - coboundary G with hc1_def
  have hc1D : derivative c1 = 0 := by
    rw [hc1_def, derivative_sub, hD, derivative_coboundary, hG, sub_self]
  have hc1 : IsCocycle c1 := hc.sub (isCocycle_coboundary G)
  have hs1 : Bivariate.swap c1 = c1 := by rw [hc1_def, map_sub, hs, swap_coboundary]
  have h01 : c1.coeff 0 = 0 := by
    rw [hc1_def, coeff_sub, h0, coeff_zero_coboundary, hG0, C_0, neg_zero, sub_zero]
  have hφ1 : powerSum p c1 = 0 := by
    rw [hc1_def, powerSum_sub, hφ, powerSum_coboundary, sub_zero]
  have hdeg1 : c1.natDegree ≤ N := by
    rw [hc1_def]
    refine (natDegree_sub_le _ _).trans (max_le hN ?_)
    have hg : g.natDegree ≤ N := natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
      rw [hg_def, hsym, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hN hm), coeff_zero]
    exact (natDegree_coboundary_le G).trans (by omega)
  -- `c1` is a `p`-th power.
  have hdY : ∀ n, ¬ p ∣ n → c1.coeff n = 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero p)
    have := congrArg (fun q => q.coeff (n - 1)) hc1D
    simp only [coeff_derivative, coeff_zero] at this
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] at this
    have hcast : ((n - 1 : ℕ) : k[X]) + 1 ≠ 0 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
      intro h
      exact hn ((CharP.cast_eq_zero_iff k[X] p n).mp h)
    exact (mul_eq_zero.mp this).resolve_right hcast
  have hdX : ∀ m n, ¬ p ∣ m → (c1.coeff n).coeff m = 0 := by
    intro m n hm
    have := coeff_coeff_swap c1 m n
    rw [hs1] at this
    rw [this, hdY m hm, coeff_zero]
  obtain ⟨c4, hc4⟩ : ∃ c4 : k[X][X], c4 ^ p = c1 := by
    refine exists_pow_eq_of_coeff p c1 hdY fun n => ?_
    refine exists_pow_eq_of_coeff p (c1.coeff n) (fun m hm => hdX m n hm) fun m => ?_
    obtain ⟨b, hb⟩ := surjective_frobenius k p ((c1.coeff n).coeff m)
    exact ⟨b, by rwa [frobenius_def] at hb⟩
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hcc4 : IsCocycle c4 := by
    have := hc1
    rw [IsCocycle, ← hc4, defect_pow] at this
    exact (pow_eq_zero_iff hp0).mp this
  have hs4 : Bivariate.swap c4 = c4 := by
    apply frobenius_inj k[X][X] p
    simp only [frobenius_def]
    rw [← map_pow, hc4, hs1]
  have h04 : c4.coeff 0 = 0 := by
    have := h01
    rw [← hc4, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero] at this
    exact (pow_eq_zero_iff hp0).mp this
  have hφ4 : powerSum p c4 = 0 := by
    have := hφ1
    rw [← hc4, powerSum_pow] at this
    exact (pow_eq_zero_iff hp0).mp this
  have hdeg4 : c4.natDegree < N := by
    have h := hdeg1
    rw [← hc4, natDegree_pow] at h
    have := Nat.mul_le_mul_right c4.natDegree h2
    omega
  obtain ⟨F, hF⟩ := ih _ hdeg4 c4 le_rfl hcc4 hs4 h04 hφ4
  refine ⟨F ^ p + G, ?_⟩
  rw [coboundary_add, coboundary_pow, ← hF, hc4, hc1_def, sub_add_cancel]

end Main

end Langlands.GroupScheme.Unipotent.OneDimensional
