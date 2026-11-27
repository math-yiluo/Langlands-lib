import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Congruent quasi-unipotent endomorphisms are unipotent

Let `ℓ` be a prime and `M` a module without `ℓ`-torsion in which no nonzero element is
divisible by every power of `ℓ`. An endomorphism `σ` of `M` with `σ ≡ 1` modulo `ℓ ^ a`,
where `ℓ ^ a ≥ 3`, and with some positive power `σ ^ m` unipotent, is itself unipotent.
This is a quasi-unipotent variant of the lemma of Minkowski and Serre on automorphisms of
finite order, which enters the proof of Raynaud's criterion of semistable reduction in
SGA 7 I, Exposé IX, 4.7.1 and 4.7.3.
-/

open Finset

namespace Langlands.LinearAlgebra.CongruentQuasiUnipotent

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Every value of the endomorphism `f` is `k` times an element of `M`. -/
def ValuesDivisible (k : ℕ) (f : Module.End R M) : Prop :=
  ∀ x : M, ∃ y : M, f x = k • y

namespace ValuesDivisible

variable {k : ℕ} {f g : Module.End R M}

theorem zero (k : ℕ) : ValuesDivisible k (0 : Module.End R M) :=
  fun _ => ⟨0, by simp⟩

theorem add (hf : ValuesDivisible k f) (hg : ValuesDivisible k g) :
    ValuesDivisible k (f + g) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  obtain ⟨z, hz⟩ := hg x
  exact ⟨y + z, by rw [LinearMap.add_apply, hy, hz, smul_add]⟩

theorem neg (hf : ValuesDivisible k f) : ValuesDivisible k (-f) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨-y, by rw [LinearMap.neg_apply, hy, smul_neg]⟩

theorem sub (hf : ValuesDivisible k f) (hg : ValuesDivisible k g) :
    ValuesDivisible k (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem sum {ι : Type*} (s : Finset ι) (F : ι → Module.End R M)
    (h : ∀ i ∈ s, ValuesDivisible k (F i)) : ValuesDivisible k (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (R := R) (M := M) k
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Composition on the left preserves divisibility of the values. -/
theorem mul_left (g : Module.End R M) (hf : ValuesDivisible k f) :
    ValuesDivisible k (g * f) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨g y, by rw [Module.End.mul_apply, hy, map_nsmul]⟩

/-- Composition on the right preserves divisibility of the values. -/
theorem mul_right (g : Module.End R M) (hf : ValuesDivisible k f) :
    ValuesDivisible k (f * g) :=
  fun x => hf (g x)

theorem mul {j : ℕ} (hf : ValuesDivisible j f) (hg : ValuesDivisible k g) :
    ValuesDivisible (j * k) (f * g) := by
  intro x
  obtain ⟨y, hy⟩ := hg x
  obtain ⟨z, hz⟩ := hf y
  exact ⟨z, by rw [Module.End.mul_apply, hy, map_nsmul, hz, smul_smul, mul_comm]⟩

theorem of_dvd {d : ℕ} (hd : d ∣ k) (hf : ValuesDivisible k f) : ValuesDivisible d f := by
  obtain ⟨c, rfl⟩ := hd
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨c • y, by rw [hy, smul_smul]⟩

theorem nsmul (c : ℕ) (hf : ValuesDivisible k f) : ValuesDivisible (c * k) (c • f) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y, by rw [LinearMap.smul_apply, hy, smul_smul]⟩

/-- If `σ ≡ 1`, then `σ ^ i ≡ 1`. -/
theorem pow_sub_one {σ : Module.End R M} (hσ : ValuesDivisible k (σ - 1)) (i : ℕ) :
    ValuesDivisible k (σ ^ i - 1) := by
  induction i with
  | zero => simpa using zero (R := R) (M := M) k
  | succ i ih =>
    have h : σ ^ (i + 1) - 1 = σ * (σ ^ i - 1) + (σ - 1) := by
      rw [pow_succ', mul_sub, mul_one]
      abel
    rw [h]
    exact (ih.mul_left σ).add hσ

/-- If `σ ≡ 1`, then `1 + σ + ⋯ + σ ^ (m - 1) ≡ m`. -/
theorem geomSum_sub {σ : Module.End R M} (hσ : ValuesDivisible k (σ - 1)) (m : ℕ) :
    ValuesDivisible k ((∑ i ∈ range m, σ ^ i) - m • (1 : Module.End R M)) := by
  have h : (∑ i ∈ range m, σ ^ i) - m • (1 : Module.End R M) =
      ∑ i ∈ range m, (σ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [h]
  exact sum _ _ fun i _ => hσ.pow_sub_one i

end ValuesDivisible

section Injective

variable (ℓ : ℕ)

/-- An endomorphism whose kernel lies in `ℓ • M` is injective, when `M` has no `ℓ`-torsion
and no nonzero element of `M` is divisible by every power of `ℓ`. -/
theorem injective_of_ker_subset (htf : ∀ x : M, ℓ • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ j : ℕ, ∃ y : M, x = ℓ ^ j • y) → x = 0)
    (S : Module.End R M) (hS : ∀ x : M, S x = 0 → ∃ y : M, x = ℓ • y) :
    Function.Injective S := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply hsep
  intro j
  induction j generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ j ih =>
    obtain ⟨y, rfl⟩ := hS x hx
    have hy : S y = 0 := htf _ (by rw [← map_nsmul, hx])
    obtain ⟨z, hz⟩ := ih y hy
    exact ⟨z, by rw [hz, smul_smul, pow_succ']⟩

/-- If `X` commutes with an injective `S` and `X * S` is nilpotent, then `X` is nilpotent. -/
theorem isNilpotent_of_isNilpotent_mul {X S : Module.End R M} (hc : Commute X S)
    (hS : Function.Injective S) (h : IsNilpotent (X * S)) : IsNilpotent X := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [hc.mul_pow, ((hc.pow_pow N N).eq)] at hN
  have hinj : Function.Injective (S ^ N) := by
    rw [Module.End.coe_pow]
    exact hS.iterate N
  ext x
  apply hinj
  have hx := LinearMap.congr_fun hN x
  rw [Module.End.mul_apply] at hx
  rw [hx]
  simp

end Injective

section Steps

variable (ℓ : ℕ)

/-- `σ - 1` commutes with every geometric sum of powers of `σ`. -/
theorem commute_sub_one_geomSum (σ : Module.End R M) (m : ℕ) :
    Commute (σ - 1) (∑ i ∈ range m, σ ^ i) :=
  Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl σ).pow_right i).sub_left (Commute.one_left _)

/-- The prime-to-`ℓ` step: if `σ ≡ 1` modulo `ℓ` and `σ ^ c` is unipotent for some `c`
prime to `ℓ`, then `σ` is unipotent. -/
theorem isNilpotent_sub_one_of_coprime (htf : ∀ x : M, ℓ • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ j : ℕ, ∃ y : M, x = ℓ ^ j • y) → x = 0)
    {σ : Module.End R M} (hσ : ValuesDivisible ℓ (σ - 1)) {c : ℕ} (hc : Nat.Coprime c ℓ)
    (h : IsNilpotent (σ ^ c - 1)) : IsNilpotent (σ - 1) := by
  set S : Module.End R M := ∑ i ∈ range c, σ ^ i
  have hXS : (σ - 1) * S = σ ^ c - 1 := mul_geom_sum σ c
  refine isNilpotent_of_isNilpotent_mul (commute_sub_one_geomSum σ c)
    (injective_of_ker_subset ℓ htf hsep S ?_) (hXS ▸ h)
  intro x hx
  obtain ⟨z, hz⟩ := hσ.geomSum_sub c x
  rw [LinearMap.sub_apply, hx, LinearMap.smul_apply, Module.End.one_apply, zero_sub] at hz
  -- `c • x = ℓ • (-z)`; Bezout gives `x ∈ ℓ • M`.
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hc
  refine ⟨u • (-z) + v • x, ?_⟩
  have hcx : (c : ℤ) • x = (ℓ : ℤ) • (-z) := by
    rw [natCast_zsmul, natCast_zsmul, smul_neg, ← hz, neg_neg]
  calc x = (u * c + v * ℓ : ℤ) • x := by rw [huv, one_smul]
    _ = u • ((c : ℤ) • x) + (ℓ : ℤ) • (v • x) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
    _ = ℓ • (u • (-z) + v • x) := by
        rw [hcx, smul_comm u (ℓ : ℤ), ← smul_add, natCast_zsmul]

/-- The `ℓ` step: if `σ ≡ 1` modulo `ℓ ^ a` with `ℓ ^ a ≥ 3` and `σ ^ ℓ` is unipotent, then
`σ` is unipotent. -/
theorem isNilpotent_sub_one_of_pow_prime [hℓ : Fact ℓ.Prime] (htf : ∀ x : M, ℓ • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ j : ℕ, ∃ y : M, x = ℓ ^ j • y) → x = 0)
    {a : ℕ} (h3 : 3 ≤ ℓ ^ a) {σ : Module.End R M} (hσ : ValuesDivisible (ℓ ^ a) (σ - 1))
    (h : IsNilpotent (σ ^ ℓ - 1)) : IsNilpotent (σ - 1) := by
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at h3
    · exact ha
  set S : Module.End R M := ∑ i ∈ range ℓ, σ ^ i
  have hXS : (σ - 1) * S = σ ^ ℓ - 1 := mul_geom_sum σ ℓ
  -- `S - ℓ = (σ - 1) * ∑_{i < ℓ} G i` with `G i = 1 + σ + ⋯ + σ ^ (i - 1)`.
  set G : ℕ → Module.End R M := fun i => ∑ k ∈ range i, σ ^ k
  set t : ℕ := ∑ i ∈ range ℓ, i
  have hS : S - ℓ • (1 : Module.End R M) =
      t • (σ - 1) + (σ - 1) * ∑ i ∈ range ℓ, (G i - i • (1 : Module.End R M)) := by
    have h1 : S - ℓ • (1 : Module.End R M) = ∑ i ∈ range ℓ, (σ ^ i - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have h2 : ∑ i ∈ range ℓ, (σ ^ i - 1) = (σ - 1) * ∑ i ∈ range ℓ, G i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_geom_sum σ i).symm
    have h3' : ∑ i ∈ range ℓ, G i =
        t • (1 : Module.End R M) + ∑ i ∈ range ℓ, (G i - i • (1 : Module.End R M)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
      abel
    rw [h1, h2, h3', mul_add, mul_smul_comm, mul_one]
  have hdiv : ValuesDivisible (ℓ ^ 2) (S - ℓ • (1 : Module.End R M)) := by
    rw [hS]
    refine ValuesDivisible.add ?_ ?_
    · refine (hσ.nsmul t).of_dvd ?_
      -- `ℓ ^ 2 ∣ t * ℓ ^ a`
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · have ha1 : a = 1 := by omega
        subst ha1
        have hodd : ℓ ≠ 2 := by
          rintro rfl
          norm_num at h3
        have ht : t * 2 = ℓ * (ℓ - 1) := Finset.sum_range_id_mul_two ℓ
        have hℓt : ℓ ∣ t := by
          have h2ℓ : Nat.Coprime 2 ℓ :=
            (Nat.coprime_primes Nat.prime_two hℓ.out).mpr (Ne.symm hodd)
          have : ℓ ∣ t * 2 := ht ▸ dvd_mul_right ℓ (ℓ - 1)
          exact (Nat.Coprime.dvd_mul_right h2ℓ.symm).mp this
        rw [pow_two, pow_one]
        exact mul_dvd_mul hℓt dvd_rfl
      · exact Dvd.dvd.mul_left (pow_dvd_pow ℓ ha2) t
    · have hE : ValuesDivisible (ℓ ^ a)
          (∑ i ∈ range ℓ, (G i - i • (1 : Module.End R M))) :=
        ValuesDivisible.sum _ _ fun i _ => hσ.geomSum_sub i
      refine (hσ.mul hE).of_dvd ?_
      rw [← pow_add]
      exact pow_dvd_pow ℓ (by omega)
  refine isNilpotent_of_isNilpotent_mul (commute_sub_one_geomSum σ ℓ)
    (injective_of_ker_subset ℓ htf hsep S ?_) (hXS ▸ h)
  intro x hx
  obtain ⟨z, hz⟩ := hdiv x
  rw [LinearMap.sub_apply, hx, LinearMap.smul_apply, Module.End.one_apply, zero_sub] at hz
  refine ⟨-z, ?_⟩
  have h0 : ℓ • (x - ℓ • -z) = 0 := by
    rw [smul_sub, smul_neg, smul_neg, smul_smul, ← pow_two, ← hz, sub_neg_eq_add,
      add_neg_cancel]
  exact sub_eq_zero.mp (htf _ h0)

end Steps

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- Iterating the `ℓ` step. -/
theorem isNilpotent_sub_one_of_pow_prime_pow (htf : ∀ x : M, ℓ • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ j : ℕ, ∃ y : M, x = ℓ ^ j • y) → x = 0)
    {a : ℕ} (h3 : 3 ≤ ℓ ^ a) (k : ℕ) :
    ∀ σ : Module.End R M, ValuesDivisible (ℓ ^ a) (σ - 1) →
      IsNilpotent (σ ^ (ℓ ^ k) - 1) → IsNilpotent (σ - 1) := by
  induction k with
  | zero => intro σ _ h; simpa using h
  | succ k ih =>
    intro σ hσ h
    have h' : IsNilpotent ((σ ^ ℓ) ^ (ℓ ^ k) - 1) := by
      rwa [← pow_mul, ← pow_succ']
    exact isNilpotent_sub_one_of_pow_prime ℓ htf hsep h3 hσ
      (ih (σ ^ ℓ) (hσ.pow_sub_one ℓ) h')

/-- **Congruent quasi-unipotent endomorphisms are unipotent.** Let `ℓ` be a prime and `M`
a module without `ℓ`-torsion in which no nonzero element is divisible by all powers of
`ℓ`. If `σ ≡ 1` modulo `ℓ ^ a` with `ℓ ^ a ≥ 3` and `σ ^ m - 1` is nilpotent for some
`m > 0`, then `σ - 1` is nilpotent. -/
theorem isNilpotent_sub_one_of_isNilpotent_pow_sub_one
    (htf : ∀ x : M, ℓ • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ j : ℕ, ∃ y : M, x = ℓ ^ j • y) → x = 0)
    {a : ℕ} (h3 : 3 ≤ ℓ ^ a) {σ : Module.End R M} (hσ : ValuesDivisible (ℓ ^ a) (σ - 1))
    {m : ℕ} (hm : 0 < m) (h : IsNilpotent (σ ^ m - 1)) : IsNilpotent (σ - 1) := by
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at h3
    · exact ha
  obtain ⟨k, c, hc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.ne_one
  have hcop : Nat.Coprime c ℓ := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hc))
  have hσk : ValuesDivisible (ℓ ^ a) (σ ^ (ℓ ^ k) - 1) := hσ.pow_sub_one _
  have hk : IsNilpotent (σ ^ (ℓ ^ k) - 1) := by
    refine isNilpotent_sub_one_of_coprime ℓ htf hsep
      (hσk.of_dvd (dvd_pow_self ℓ (by omega))) hcop ?_
    rwa [← pow_mul]
  exact isNilpotent_sub_one_of_pow_prime_pow ℓ htf hsep h3 k σ hσ hk

end Langlands.LinearAlgebra.CongruentQuasiUnipotent
