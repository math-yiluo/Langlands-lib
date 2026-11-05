import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionProof
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormHensel

/-! # Unit norm surjectivity for a Galois extension of prime degree

Let `C / B` be a finite Galois extension of prime degree `p` and let `w` be a real valuation on
`C` that is invariant under `Gal(C/B)`. Assume that the restriction of `w` to `B` is discrete
with a uniformizer `π`, satisfies Hensel's lemma for simple roots, and has root finding modulo
the maximal ideal, and that every integral element of `C` is congruent modulo the maximal ideal
to an integral element of `B`. Then every unit of `B` is the norm of a unit of `C`.

The proof works with the expansion `N(1 + b x) = ∑ c_k b^k`. In this expansion `c_0 = 1`,
`c_1 = Tr x` and `c_p = N x`, and for `0 < k < p` the coefficient `c_k` is the trace of an
element of value at most `w x ^ k`. A strong Hensel lemma makes the norm group of units open.
Root finding modulo the maximal ideal then approximates any unit by norms, one level of the
unit filtration at a time.
-/

noncomputable section

open Polynomial Finset Module
open scoped NNReal Pointwise

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

open Langlands.LocalClassField.PrimeOrbitProductTraceExpansionProof

/-- If `0 < γ < 1` and `0 < b`, some power `γ ^ m` satisfies `γ ^ m * a ≤ b`. -/
theorem exists_pow_mul_le {γ : ℝ≥0} (hγ1 : γ < 1) (a : ℝ≥0) {b : ℝ≥0}
    (hb : 0 < b) : ∃ m : ℕ, γ ^ m * a ≤ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  obtain ⟨m, hm⟩ := NNReal.exists_pow_lt_of_lt_one (div_pos hb (pos_iff_ne_zero.mpr ha)) hγ1
  exact ⟨m, ((lt_div_iff₀ (pos_iff_ne_zero.mpr ha)).mp hm).le⟩

section General

variable {C : Type*} [Field C] (w : Valuation C ℝ≥0)

/-- The additive submonoid of elements of value at most `r`. -/
def valLE (r : ℝ≥0) : AddSubmonoid C where
  carrier := {y | w y ≤ r}
  zero_mem' := by simp
  add_mem' := fun ha hb => (w.map_add _ _).trans (max_le ha hb)

variable {w}

theorem val_one_add {z : C} (hz : w z < 1) : w (1 + z) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left] <;> simp [hz]

end General

variable {B C : Type*} [Field B] [Field C] [Algebra B C]

/-- The hypotheses of the cyclic step for a valuation `w` on `C` and a uniformizer `π` of `B`. -/
structure CyclicHyp (w : Valuation C ℝ≥0) (π : B) : Prop where
  inv : ∀ (σ : Gal(C/B)) (x : C), w (σ x) = w x
  prime : (finrank B C).Prime
  hensel : ValHensel (w.comap (algebraMap B C))
  residueRoot : ValResidueRoot (w.comap (algebraMap B C))
  unif : ValUniformizer (w.comap (algebraMap B C)) π
  res : ∀ x : C, w x ≤ 1 → ∃ c : B, w (algebraMap B C c) ≤ 1 ∧ w (x - algebraMap B C c) < 1

theorem card_gal [FiniteDimensional B C] [IsGalois B C] :
    Fintype.card Gal(C/B) = finrank B C := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

namespace CyclicHyp

variable {w : Valuation C ℝ≥0} {π : B} (h : CyclicHyp w π)

include h

theorem two_le : 2 ≤ finrank B C := h.prime.two_le

theorem gamma_pos : 0 < w (algebraMap B C π) := h.unif.1

theorem gamma_lt_one : w (algebraMap B C π) < 1 := h.unif.2.1

theorem pi_ne_zero : π ≠ 0 := by
  intro h0
  have := h.gamma_pos
  rw [h0, map_zero, map_zero] at this
  exact lt_irrefl _ this

/-- Nonzero integral elements of `B` have value a power of `γ = w π`. -/
theorem val_eq_pow {b : B} (hb0 : b ≠ 0) (hb : w (algebraMap B C b) ≤ 1) :
    ∃ k : ℕ, w (algebraMap B C b) = w (algebraMap B C π) ^ k :=
  h.unif.2.2 b hb0 hb

/-- Discreteness: a value of `B` below `γ ^ n` is at most `γ ^ (n + 1)`. -/
theorem le_pow_succ_of_lt {b : B} {n : ℕ} (hb : w (algebraMap B C b) < w (algebraMap B C π) ^ n) :
    w (algebraMap B C b) ≤ w (algebraMap B C π) ^ (n + 1) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  have hle : w (algebraMap B C b) ≤ 1 :=
    hb.le.trans (pow_le_one₀ zero_le h.gamma_lt_one.le)
  obtain ⟨k, hk⟩ := h.val_eq_pow hb0 hle
  rw [hk] at hb ⊢
  have := (pow_lt_pow_iff_right_of_lt_one₀ h.gamma_pos h.gamma_lt_one).mp hb
  exact pow_le_pow_of_le_one zero_le h.gamma_lt_one.le this

/-- A value of `B` strictly between `γ ^ (n + 1)` and `γ ^ n` (inclusive) equals `γ ^ n`. -/
theorem eq_pow_of_lt_of_le {b : B} {n : ℕ}
    (h1 : w (algebraMap B C π) ^ (n + 1) < w (algebraMap B C b))
    (h2 : w (algebraMap B C b) ≤ w (algebraMap B C π) ^ n) :
    w (algebraMap B C b) = w (algebraMap B C π) ^ n := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at h1
  have hle : w (algebraMap B C b) ≤ 1 := h2.trans (pow_le_one₀ zero_le h.gamma_lt_one.le)
  obtain ⟨k, hk⟩ := h.val_eq_pow hb0 hle
  rw [hk] at h1 h2 ⊢
  have hk1 := (pow_lt_pow_iff_right_of_lt_one₀ h.gamma_pos h.gamma_lt_one).mp h1
  have hk2 := (pow_le_pow_iff_right_of_lt_one₀ h.gamma_pos h.gamma_lt_one).mp h2
  rw [show k = n by omega]

variable [FiniteDimensional B C] [IsGalois B C]

theorem val_norm (x : C) : w (algebraMap B C (Algebra.norm B x)) = w x ^ finrank B C := by
  rw [Algebra.norm_eq_prod_automorphisms, map_prod]
  simp only [h.inv, prod_const, card_univ, card_gal]

theorem val_trace_le (x : C) : w (algebraMap B C (Algebra.trace B C x)) ≤ w x := by
  rw [trace_eq_sum_automorphisms]
  exact w.map_sum_le fun σ _ => (h.inv σ x).le

/-- The expansion of the norm of `1 + b x` in powers of `b`. -/
theorem norm_one_add_expansion (x : C) :
    ∃ c : ℕ → B, c 0 = 1 ∧ c 1 = Algebra.trace B C x ∧ c (finrank B C) = Algebra.norm B x ∧
      (∀ k ∈ Ico 1 (finrank B C), ∃ z : C, w z ≤ w x ^ k ∧ c k = Algebra.trace B C z) ∧
      (∀ k, w (algebraMap B C (c k)) ≤ w x ^ k) ∧
      ∀ b : B, Algebra.norm B (1 + algebraMap B C b * x) =
        ∑ k ∈ range (finrank B C + 1), c k * b ^ k := by
  classical
  set p := finrank B C with hp_def
  have hp2 : 2 ≤ p := h.two_le
  have hpG : (Fintype.card Gal(C/B)).Prime := by rw [card_gal]; exact h.prime
  -- the elementary symmetric functions of the conjugates
  set E : ℕ → C := fun k =>
    ∑ S ∈ powersetCard k (univ : Finset Gal(C/B)), ∏ g ∈ S, g x with hE
  have hE1 : E 1 = algebraMap B C (Algebra.trace B C x) := by
    rw [trace_eq_sum_automorphisms, hE]
    simp only [powersetCard_one, sum_map, Function.Embedding.coeFn_mk, prod_singleton]
  have horbit : ∀ k ∈ Ico 1 p, ∃ z : C, w z ≤ w x ^ k ∧ E k = ∑ g : Gal(C/B), g z := by
    intro k hk
    have hk := mem_Ico.mp hk
    obtain ⟨z, hzP, hz⟩ := exists_mem_sum_eq_sum_smul (G := Gal(C/B))
      (fun S => ∏ g ∈ S, g • x) (fun k S => prod_smul_smul_finset x k S) (valLE w (w x ^ k))
      (powersetCard k univ)
      (fun g S hS => by
        rw [mem_powersetCard] at hS ⊢
        exact ⟨subset_univ _, by rw [card_smul_finset]; exact hS.2⟩)
      (fun S hS g g' hgg' => by
        have hS := (mem_powersetCard.mp hS).2
        refine smul_finset_injective_of_prime_card hpG S (by omega) ?_ g g' hgg'
        rw [card_gal]
        omega)
      (fun S hS => by
        have hS := (mem_powersetCard.mp hS).2
        show w (∏ g ∈ S, g • x) ≤ w x ^ k
        rw [map_prod]
        simp only [AlgEquiv.smul_def, h.inv, prod_const, hS, le_refl])
    refine ⟨z, hzP, ?_⟩
    rw [hE]
    simpa only [AlgEquiv.smul_def] using hz
  choose! z hz using horbit
  set c : ℕ → B := fun k =>
    if k = 0 then 1 else if k = 1 then Algebra.trace B C x else if k = p then Algebra.norm B x
      else if k < p then Algebra.trace B C (z k) else 0 with hc
  have hc0 : c 0 = 1 := by simp [hc]
  have hc1 : c 1 = Algebra.trace B C x := by simp [hc]
  have hcp : c p = Algebra.norm B x := by
    simp only [hc, show p ≠ 0 by omega, show p ≠ 1 by omega, ite_false, ite_true]
  have hcmid : ∀ k ∈ Ico 1 p, ∃ y : C, w y ≤ w x ^ k ∧ c k = Algebra.trace B C y := by
    intro k hk
    have hk' := mem_Ico.mp hk
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨x, by simp, hc1⟩
    · refine ⟨z k, (hz k hk).1, ?_⟩
      simp only [hc, show k ≠ 0 by omega, hk1, show k ≠ p by omega, hk'.2, ite_false, ite_true]
  refine ⟨c, hc0, hc1, hcp, hcmid, ?_, ?_⟩
  · intro k
    rcases Nat.lt_or_ge k p with hkp | hkp
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [hc0]
      · obtain ⟨y, hy, hcy⟩ := hcmid k (mem_Ico.mpr ⟨hk0, hkp⟩)
        rw [hcy]
        exact (h.val_trace_le y).trans hy
    · rcases eq_or_lt_of_le hkp with rfl | hkp'
      · rw [hcp, h.val_norm]
      · simp only [hc, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ p by omega,
          show ¬ k < p by omega, ite_false, map_zero, zero_le]
  · intro b
    apply (algebraMap B C).injective
    have hEk : ∀ k ∈ range (p + 1), algebraMap B C (c k) = E k := by
      intro k hk
      have hk := mem_range.mp hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [hc0, map_one, hE]
        simp
      by_cases hk1 : k = 1
      · subst hk1
        rw [hc1, hE1]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hkp
      · rw [hcp, Algebra.norm_eq_prod_automorphisms, hE]
        simp only
        rw [hp_def, ← card_gal, ← card_univ, powersetCard_self, sum_singleton]
      · have hy := (hz k (mem_Ico.mpr ⟨hk0, hkp⟩)).2
        simp only [hc, show k ≠ 0 by omega, hk1, show k ≠ p by omega, hkp, ite_false, ite_true]
        rw [trace_eq_sum_automorphisms, hy]
    rw [Algebra.norm_eq_prod_automorphisms, map_sum]
    have hprod : ∏ σ : Gal(C/B), σ (1 + algebraMap B C b * x) =
        ∏ σ : Gal(C/B), (1 + algebraMap B C b * σ x) := by
      refine prod_congr rfl fun σ _ => ?_
      rw [map_add, map_one, map_mul, AlgEquiv.commutes]
    rw [hprod, prod_one_add, sum_powerset, card_univ, card_gal]
    refine sum_congr rfl fun k hk => ?_
    rw [map_mul, map_pow, hEk k hk, hE, mul_comm, mul_sum]
    refine sum_congr rfl fun S hS => ?_
    rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hS).2]

/-- There is an element of `C` whose value is a `p`-th root of `γ`: the extension is totally
ramified. Otherwise all values of `C` lie in the value group of `B`, every integral element of
`C` is approximated arbitrarily well by elements of `B`, and a Krasner-type argument shows that
every element of `C` is fixed by `Gal(C/B)`. -/
theorem exists_val_pow_eq : ∃ πL : C, w πL ^ finrank B C = w (algebraMap B C π) := by
  set p := finrank B C
  set γ := w (algebraMap B C π) with hγ
  have hγ0 : 0 < γ := h.gamma_pos
  have hγ1 : γ < 1 := h.gamma_lt_one
  have hp0 : p ≠ 0 := h.prime.ne_zero
  by_contra hno
  push Not at hno
  -- Step 1: every value below `1` is at most `γ`.
  have hsmall : ∀ y : C, w y < 1 → w y ≤ γ := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hN0 : Algebra.norm B y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy0
    have hNle : w (algebraMap B C (Algebra.norm B y)) ≤ 1 := by
      rw [h.val_norm]
      exact pow_le_one₀ zero_le hy.le
    obtain ⟨k, hk⟩ := h.val_eq_pow hN0 hNle
    rw [h.val_norm] at hk
    by_cases hpk : p ∣ k
    · obtain ⟨k', rfl⟩ := hpk
      rw [mul_comm p k', pow_mul] at hk
      have hyk : w y = γ ^ k' := (pow_left_inj₀ zero_le zero_le hp0).mp
        hk
      rcases Nat.eq_zero_or_pos k' with rfl | hk'
      · rw [hyk, pow_zero] at hy
        exact absurd hy (lt_irrefl _)
      · rw [hyk]
        exact pow_le_of_le_one zero_le hγ1.le hk'.ne'
    · exfalso
      have hcop : Nat.Coprime k p :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hpk))
      obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := p) hcop h.prime.one_lt
      obtain ⟨b, hka⟩ : ∃ b, k * a = p * b + 1 :=
        ⟨k * a / p, by rw [← ha]; exact (Nat.div_add_mod _ _).symm⟩
      apply hno (y ^ a / algebraMap B C π ^ b)
      have hπ0 : (algebraMap B C π) ≠ 0 := by
        intro h0
        rw [hγ, h0, map_zero] at hγ0
        exact lt_irrefl _ hγ0
      rw [map_div₀, map_pow, map_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm a p, pow_mul, hk,
        ← pow_mul, hka, ← hγ, pow_add, pow_one, mul_comm b p]
      field_simp
  -- Step 2: integral elements are approximated by elements of `B`.
  have happrox : ∀ x : C, w x ≤ 1 → ∀ n : ℕ, ∃ c : B, w (x - algebraMap B C c) ≤ γ ^ n := by
    intro x hx n
    induction n with
    | zero => exact ⟨0, by simpa using hx⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      have hπn : algebraMap B C (π ^ n) ≠ 0 := by
        rw [map_pow]
        refine pow_ne_zero _ fun h0 => ?_
        rw [hγ, h0, map_zero] at hγ0
        exact lt_irrefl _ hγ0
      set y := (x - algebraMap B C c) / algebraMap B C (π ^ n)
      have hy : w y ≤ 1 := by
        rw [map_div₀, map_pow, map_pow, ← hγ]
        exact div_le_one_of_le₀ hc zero_le
      obtain ⟨c', -, hc'⟩ := h.res y hy
      refine ⟨c + π ^ n * c', ?_⟩
      have hxy : x - algebraMap B C (c + π ^ n * c') =
          algebraMap B C (π ^ n) * (y - algebraMap B C c') := by
        rw [mul_sub, mul_div_cancel₀ _ hπn, map_add, map_mul]
        ring
      rw [hxy, map_mul, map_pow, map_pow, ← hγ, pow_succ]
      exact mul_le_mul_right (hsmall _ hc') _
  -- Step 3: integral elements are fixed by the Galois group.
  have hfix : ∀ x : C, w x ≤ 1 → ∀ σ : Gal(C/B), σ x = x := by
    intro x hx σ
    have hle : ∀ n : ℕ, w (σ x - x) ≤ γ ^ n := by
      intro n
      obtain ⟨c, hc⟩ := happrox x hx n
      have : σ x - x = σ (x - algebraMap B C c) - (x - algebraMap B C c) := by
        rw [map_sub, AlgEquiv.commutes]
        ring
      rw [this]
      refine (w.map_sub _ _).trans (max_le ?_ hc)
      rw [h.inv]
      exact hc
    by_contra hne
    have hpos : 0 < w (σ x - x) := by
      rw [pos_iff_ne_zero, Ne, Valuation.zero_iff]
      exact sub_ne_zero.mpr hne
    obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hpos hγ1
    exact absurd (hle n) (not_le.mpr hn)
  -- Step 4: then `C = B`, contradicting `p ≥ 2`.
  have hsurj : ∀ x : C, x ∈ Set.range (algebraMap B C) := by
    intro x
    obtain ⟨m, hm⟩ := exists_pow_mul_le hγ1 (w x) one_pos
    have hint : w (algebraMap B C (π ^ m) * x) ≤ 1 := by
      rwa [map_mul, map_pow, map_pow, ← hγ]
    obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr (hfix _ hint)
    have hπm : algebraMap B C (π ^ m) ≠ 0 := by
      rw [map_pow]
      refine pow_ne_zero _ fun h0 => ?_
      rw [hγ, h0, map_zero] at hγ0
      exact lt_irrefl _ hγ0
    refine ⟨c / π ^ m, ?_⟩
    rw [map_div₀, hc, mul_div_cancel_left₀ _ hπm]
  have hbot : (⊥ : IntermediateField B C) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, rfl⟩ := hsurj x
    exact IntermediateField.algebraMap_mem _ c
  have := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hbot
  have := h.two_le
  omega

/-- Openness of the norm group of units: units close enough to `1` are norms of units. The
proof takes `x₀` integral with trace `t = π ^ m` and solves `N(1 + t y x₀) = u` by the strong
Hensel lemma applied to `(1 - u) / t ^ 2 + y + ∑_{2 ≤ k ≤ p} c_k t ^ (k - 2) y ^ k = 0`. -/
theorem exists_open : ∃ M : ℕ, ∀ u : B,
    w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ M →
      ∃ x : C, w x = 1 ∧ Algebra.norm B x = u := by
  classical
  set p := finrank B C with hp_def
  have hp2 : 2 ≤ p := h.two_le
  set γ := w (algebraMap B C π) with hγ
  have hγ0 : 0 < γ := h.gamma_pos
  have hγ1 : γ < 1 := h.gamma_lt_one
  obtain ⟨x1, hx1⟩ := Algebra.trace_surjective B C 1
  obtain ⟨m, hm⟩ := exists_pow_mul_le hγ1 (w x1) one_pos
  set t : B := π ^ m with ht
  have htv : w (algebraMap B C t) = γ ^ m := by rw [ht, map_pow, map_pow]
  have htv1 : w (algebraMap B C t) ≤ 1 := by rw [htv]; exact pow_le_one₀ zero_le hγ1.le
  have ht0 : t ≠ 0 := pow_ne_zero _ h.pi_ne_zero
  set x0 : C := algebraMap B C t * x1 with hx0
  have hx0v : w x0 ≤ 1 := by rwa [hx0, map_mul, htv]
  have htr : Algebra.trace B C x0 = t := by
    rw [hx0, ← Algebra.smul_def, LinearMap.map_smul, hx1, smul_eq_mul, mul_one]
  obtain ⟨c, hc0, hc1, -, -, hcv, hN⟩ := h.norm_one_add_expansion x0
  refine ⟨2 * m + 1, fun u hu => ?_⟩
  set a0 : B := (1 - u) / t ^ 2 with ha0
  have ha0v : w (algebraMap B C a0) < 1 := by
    rw [ha0, map_div₀, map_div₀, map_pow, map_pow, htv, ← neg_sub, map_neg, Valuation.map_neg,
      ← pow_mul, mul_comm m 2]
    refine (div_lt_one (pow_pos hγ0 _)).mpr (hu.trans_lt ?_)
    exact pow_lt_pow_right_of_lt_one₀ hγ0 hγ1 (by omega)
  have hc' : ∀ k, (w.comap (algebraMap B C)) (c k * t ^ (k - 2)) ≤ 1 := by
    intro k
    rw [Valuation.comap_apply, map_mul, map_mul, map_pow, map_pow]
    exact mul_le_one' ((hcv k).trans (pow_le_one₀ zero_le hx0v)) (pow_le_one₀ zero_le htv1)
  obtain ⟨y, hy, hyeq⟩ := exists_root_one_add_of_hensel h.hensel (p + 1) (a0 := a0) ha0v hc'
  rw [Valuation.comap_apply] at hy
  refine ⟨1 + algebraMap B C (t * y) * x0, val_one_add ?_, ?_⟩
  · rw [map_mul, map_mul, map_mul]
    calc w (algebraMap B C t) * w (algebraMap B C y) * w x0
        ≤ w (algebraMap B C t) * w (algebraMap B C y) := mul_le_of_le_one_right zero_le hx0v
      _ ≤ w (algebraMap B C y) := mul_le_of_le_one_left zero_le htv1
      _ < 1 := hy
  have key : t ^ 2 * (a0 + y + ∑ k ∈ Ico 2 (p + 1), c k * t ^ (k - 2) * y ^ k) =
      (1 - u) + t * (t * y) + ∑ k ∈ Ico 2 (p + 1), c k * (t * y) ^ k := by
    rw [mul_add, mul_add, mul_sum, ha0]
    congr 1
    · field_simp
    · refine sum_congr rfl fun k hk => ?_
      have hk := (mem_Ico.mp hk).1
      have htk : t ^ k = t ^ 2 * t ^ (k - 2) := by rw [← pow_add]; congr 1; omega
      rw [mul_pow, htk]
      ring
  rw [hyeq, mul_zero] at key
  rw [hN, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1),
    sum_eq_sum_Ico_succ_bot (by omega : 0 + 1 < p + 1), hc0, hc1, htr]
  linear_combination -key

/-- The level-`n` witness: for `n ≥ 1` there is `w₁` with `w w₁ < 1` such that all
coefficients `c_k` (`1 ≤ k ≤ p`) of the expansion of `N(1 + b w₁)` have value at most `γ ^ n`
and one of them has value exactly `γ ^ n`. -/
theorem exists_witness {n : ℕ} (hn : 1 ≤ n) :
    ∃ w1 : C, w w1 < 1 ∧ ∃ c : ℕ → B, c 0 = 1 ∧
      (∀ k ∈ Ico 1 (finrank B C + 1),
        w (algebraMap B C (c k)) ≤ w (algebraMap B C π) ^ n) ∧
      (∃ k ∈ Ico 1 (finrank B C + 1),
        w (algebraMap B C (c k)) = w (algebraMap B C π) ^ n) ∧
      ∀ b : B, Algebra.norm B (1 + algebraMap B C b * w1) =
        ∑ k ∈ range (finrank B C + 1), c k * b ^ k := by
  classical
  set p := finrank B C with hp_def
  set γ := w (algebraMap B C π) with hγ
  have hγ0 : 0 < γ := h.gamma_pos
  have hγ1 : γ < 1 := h.gamma_lt_one
  have hp1 : 1 ≤ p := h.prime.one_lt.le
  obtain ⟨πL, hπL⟩ := h.exists_val_pow_eq
  rw [← hγ, ← hp_def] at hπL
  set δ := w πL with hδ
  have hδ1 : δ < 1 := by
    by_contra hge
    push Not at hge
    have := one_le_pow₀ hge (n := p)
    rw [hπL] at this
    exact absurd hγ1 (not_lt.mpr this)
  have hbound : ∀ j : ℕ, n ≤ j →
      (∀ x : C, w x ≤ δ ^ j → w (algebraMap B C (Algebra.trace B C x)) ≤ γ ^ n) →
      ∀ w1 : C, w w1 ≤ δ ^ j → w w1 < 1 → ∀ c : ℕ → B,
      (∀ k ∈ Ico 1 p, ∃ z : C, w z ≤ w w1 ^ k ∧ c k = Algebra.trace B C z) →
      (∀ k, w (algebraMap B C (c k)) ≤ w w1 ^ k) →
      ∀ k ∈ Ico 1 (p + 1), w (algebraMap B C (c k)) ≤ γ ^ n := by
    intro j hj hQ w1 hw1 hw1' c hcmid hcv k hk
    have hk := mem_Ico.mp hk
    rcases Nat.lt_or_ge k p with hkp | hkp
    · obtain ⟨z, hz, hcz⟩ := hcmid k (mem_Ico.mpr ⟨hk.1, hkp⟩)
      rw [hcz]
      exact hQ z (hz.trans ((pow_le_of_le_one zero_le hw1'.le (by omega)).trans hw1))
    · have hkp' : k = p := by omega
      rw [hkp']
      refine (hcv _).trans ?_
      calc w w1 ^ p ≤ (δ ^ j) ^ p := pow_le_pow_left₀ zero_le hw1 _
        _ = γ ^ j := by rw [← pow_mul, mul_comm, pow_mul, hπL]
        _ ≤ γ ^ n := pow_le_pow_of_le_one zero_le hγ1.le hj
  by_cases hQn : ∀ x : C, w x ≤ δ ^ n → w (algebraMap B C (Algebra.trace B C x)) ≤ γ ^ n
  · -- the uniformizer power `πL ^ n` works; its norm has value `γ ^ n`
    have hlt : w (πL ^ n) < 1 := by rw [map_pow]; exact pow_lt_one₀ zero_le hδ1 (by omega)
    obtain ⟨c, hc0, -, hcp, hcmid, hcv, hN⟩ := h.norm_one_add_expansion (πL ^ n)
    refine ⟨πL ^ n, hlt, c, hc0,
      hbound n le_rfl hQn _ (by rw [map_pow]) hlt c hcmid hcv,
      ⟨p, mem_Ico.mpr ⟨hp1, by omega⟩, ?_⟩, hN⟩
    rw [hcp, h.val_norm, map_pow, ← pow_mul, mul_comm, pow_mul, hπL]
  · -- a minimal trace level gives an element whose trace has value `γ ^ n`
    have hex : ∃ j, ∀ x : C, w x ≤ δ ^ j → w (algebraMap B C (Algebra.trace B C x)) ≤ γ ^ n :=
      ⟨p * n, fun x hx => (h.val_trace_le x).trans (hx.trans (by rw [pow_mul, hπL]))⟩
    have hQj0 := Nat.find_spec hex
    have hj0n : n < Nat.find hex := by
      by_contra hle
      push Not at hle
      exact hQn fun x hx => hQj0 x (hx.trans (pow_le_pow_of_le_one zero_le hδ1.le hle))
    have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hnot
    obtain ⟨x0, hx0, hx0tr⟩ := hnot
    set w1 := algebraMap B C π * x0 with hw1
    have hw1v : w w1 ≤ δ ^ Nat.find hex := by
      rw [hw1, map_mul]
      calc w (algebraMap B C π) * w x0 = δ ^ p * w x0 := by rw [hπL]
        _ ≤ δ ^ 1 * δ ^ (Nat.find hex - 1) :=
            mul_le_mul' (pow_le_pow_of_le_one zero_le hδ1.le hp1) hx0
        _ = δ ^ Nat.find hex := by rw [← pow_add]; congr 1; omega
    have hw1lt : w w1 < 1 := hw1v.trans_lt (pow_lt_one₀ zero_le hδ1 (by omega))
    obtain ⟨c, hc0, hc1, -, hcmid, hcv, hN⟩ := h.norm_one_add_expansion w1
    refine ⟨w1, hw1lt, c, hc0, hbound _ hj0n.le hQj0 w1 hw1v hw1lt c hcmid hcv,
      ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩, hN⟩
    have htr : Algebra.trace B C w1 = π * Algebra.trace B C x0 := by
      rw [hw1, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    rw [hc1]
    refine h.eq_pow_of_lt_of_le ?_ (hQj0 w1 hw1v)
    rw [htr, map_mul, map_mul, ← hγ, pow_succ']
    exact mul_lt_mul_of_pos_left hx0tr hγ0

/-- One improvement step: if `w (a) = γ ^ n` with `n ≥ 1`, some unit `x` of `C` has
`N x ≡ 1 + a` modulo elements of value `< γ ^ n`. Root finding modulo the maximal ideal is
applied to `-1 + ∑_{1 ≤ k ≤ p} (c_k / a) X ^ k` for the level-`n` witness. -/
theorem exists_improve {n : ℕ} (hn : 1 ≤ n) {a : B}
    (ha : w (algebraMap B C a) = w (algebraMap B C π) ^ n) :
    ∃ x : C, w x = 1 ∧
      w (algebraMap B C (Algebra.norm B x - (1 + a))) < w (algebraMap B C π) ^ n := by
  classical
  set p := finrank B C with hp_def
  set γ := w (algebraMap B C π) with hγ
  have hγ0 : 0 < γ := h.gamma_pos
  obtain ⟨w1, hw1, c, hc0, hcle, ⟨k0, hk0, hk0v⟩, hN⟩ := h.exists_witness hn
  have hγn : γ ^ n ≠ 0 := (pow_pos hγ0 n).ne'
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at ha
    exact hγn ha.symm
  set f : B[X] := -1 + ∑ k ∈ Ico 1 (p + 1), Polynomial.C (c k / a) * X ^ k with hf
  have hfint : IntPoly (w.comap (algebraMap B C)) f := by
    refine IntPoly.add ?_ (IntPoly.sum _ fun k hk => IntPoly.C_mul_X_pow ?_ _)
    · intro i
      rw [← C_1, ← C_neg, coeff_C]
      split_ifs
      · rw [Valuation.comap_apply, map_neg, Valuation.map_neg, map_one, map_one]
      · simp
    · rw [Valuation.comap_apply, map_div₀, map_div₀, ha]
      exact div_le_one_of_le₀ (hcle k hk) zero_le
  have hk0' := mem_Ico.mp hk0
  have hfk0 : f.coeff k0 = c k0 / a := by
    rw [hf, coeff_add, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true hk0), ← C_1, ← C_neg, coeff_C,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), zero_add]
  obtain ⟨b, hb1, hb2⟩ := h.residueRoot f hfint ⟨k0, by omega, by
    rw [hfk0, Valuation.comap_apply, map_div₀, map_div₀, hk0v, ha, div_self hγn]⟩
  rw [Valuation.comap_apply] at hb1 hb2
  refine ⟨1 + algebraMap B C b * w1, val_one_add ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_left zero_le hb1).trans_lt hw1
  have heval : f.eval b = -1 + ∑ k ∈ Ico 1 (p + 1), c k / a * b ^ k := by
    simp [hf, eval_finsetSum]
  have hs : ∑ k ∈ Ico 1 (p + 1), a * (c k / a * b ^ k) = ∑ k ∈ Ico 1 (p + 1), c k * b ^ k :=
    sum_congr rfl fun k _ => by field_simp
  have hNx : Algebra.norm B (1 + algebraMap B C b * w1) - (1 + a) = a * f.eval b := by
    rw [hN, heval, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1), hc0, mul_add,
      mul_sum, hs]
    ring
  rw [hNx, map_mul, map_mul, ha]
  exact mul_lt_of_lt_one_right (pow_pos hγ0 n) hb2

/-- Descent of the norm claim from level `n + 1` to level `n ≥ 1`. -/
theorem norm_claim_step {n : ℕ} (hn : 1 ≤ n)
    (hnext : ∀ u : B, w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ (n + 1) →
      ∃ x : C, w x = 1 ∧ Algebra.norm B x = u) :
    ∀ u : B, w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ n →
      ∃ x : C, w x = 1 ∧ Algebra.norm B x = u := by
  intro u hu
  by_cases hle : w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ (n + 1)
  · exact hnext u hle
  push Not at hle
  obtain ⟨x1, hx1, hx1N⟩ := h.exists_improve hn (h.eq_pow_of_lt_of_le hle hu)
  rw [show (1 : B) + (u - 1) = u by ring] at hx1N
  have hN1 : w (algebraMap B C (Algebra.norm B x1)) = 1 := by rw [h.val_norm, hx1, one_pow]
  have hN10 : Algebra.norm B x1 ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hN1
    exact zero_ne_one hN1
  have hq : w (algebraMap B C (u / Algebra.norm B x1 - 1)) ≤ w (algebraMap B C π) ^ (n + 1) := by
    have : u / Algebra.norm B x1 - 1 = -(Algebra.norm B x1 - u) / Algebra.norm B x1 := by
      field_simp
      ring
    rw [this, map_div₀, map_div₀, hN1, div_one, map_neg, Valuation.map_neg]
    exact h.le_pow_succ_of_lt hx1N
  obtain ⟨x2, hx2, hx2N⟩ := hnext (u / Algebra.norm B x1) hq
  refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, one_mul], ?_⟩
  rw [map_mul, hx2N]
  field_simp

omit [FiniteDimensional B C] [IsGalois B C] in
/-- Level zero: every unit is a `p`-th power times a unit congruent to `1` modulo `π`. -/
theorem norm_claim_zero
    (h1 : ∀ u : B, w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ 1 →
      ∃ x : C, w x = 1 ∧ Algebra.norm B x = u) :
    ∀ u : B, w (algebraMap B C u) = 1 → ∃ x : C, w x = 1 ∧ Algebra.norm B x = u := by
  classical
  set p := finrank B C with hp_def
  have hp0 : p ≠ 0 := h.prime.ne_zero
  intro u hu
  set f : B[X] := X ^ p - Polynomial.C u with hf
  have hfint : IntPoly (w.comap (algebraMap B C)) f := by
    intro i
    rw [hf, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs <;> first | omega | simp [Valuation.comap_apply, hu]
  obtain ⟨b, hb1, hb2⟩ := h.residueRoot f hfint ⟨p, Nat.pos_of_ne_zero hp0, by
    rw [hf, coeff_sub, coeff_X_pow, coeff_C, ite_eq_left_of_eq_true _ _ (eq_true rfl),
      ite_eq_right_of_eq_false _ _ (eq_false hp0), sub_zero, map_one]⟩
  rw [Valuation.comap_apply] at hb1 hb2
  have hfb : f.eval b = b ^ p - u := by simp [hf]
  rw [hfb] at hb2
  have hbp : w (algebraMap B C (b ^ p)) = 1 := by
    rw [show b ^ p = u + (b ^ p - u) by ring, map_add, Valuation.map_add_eq_of_lt_left, hu]
    rwa [hu]
  have hb : w (algebraMap B C b) = 1 := by
    rw [map_pow, map_pow] at hbp
    exact (pow_left_inj₀ zero_le zero_le hp0).mp (by rw [hbp, one_pow])
  have hb0 : b ^ p ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hbp
    exact zero_ne_one hbp
  have hq : w (algebraMap B C (u / b ^ p - 1)) ≤ w (algebraMap B C π) ^ 1 := by
    have : u / b ^ p - 1 = -(b ^ p - u) / b ^ p := by
      field_simp
      ring
    rw [this, map_div₀, map_div₀, hbp, div_one, map_neg, Valuation.map_neg]
    exact h.le_pow_succ_of_lt (n := 0) (by rwa [pow_zero])
  obtain ⟨x, hx, hxN⟩ := h1 (u / b ^ p) hq
  refine ⟨x * algebraMap B C b, by rw [map_mul, hx, hb, one_mul], ?_⟩
  rw [map_mul, hxN, Algebra.norm_algebraMap, ← hp_def]
  field_simp

/-- **Cyclic step.** Every unit of `B` is the norm of a unit of `C`. -/
theorem exists_norm_eq (u : B) (hu : w (algebraMap B C u) = 1) :
    ∃ x : C, w x = 1 ∧ Algebra.norm B x = u := by
  obtain ⟨M, hM⟩ := h.exists_open
  have hall : ∀ d n : ℕ, M ≤ n + d → 1 ≤ n →
      ∀ u : B, w (algebraMap B C (u - 1)) ≤ w (algebraMap B C π) ^ n →
        ∃ x : C, w x = 1 ∧ Algebra.norm B x = u := by
    intro d
    induction d with
    | zero =>
      intro n hn _ u hu
      exact hM u (hu.trans (pow_le_pow_of_le_one zero_le h.gamma_lt_one.le (by omega)))
    | succ d ih =>
      intro n hn h1
      exact h.norm_claim_step h1 (ih (n + 1) (by omega) (by omega))
  exact h.norm_claim_zero (hall M 1 (by omega) le_rfl) u hu

end CyclicHyp

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
