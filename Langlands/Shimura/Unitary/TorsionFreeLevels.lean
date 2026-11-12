import Langlands.Shimura.Unitary.Adelic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Torsion-free principal congruence levels

Let `A` be a finite-dimensional `ℚ`-algebra with involution `σ`, `v` a finite place of `ℚ` and
`q ≥ 3` the prime below `v`. This module constructs an open subgroup of `σ(ℚ_v)` whose only
element of finite order is `1`: the principal congruence level modulo `q`.

* Generic algebra (`powMul Λ q k = q^k Λ`): if `Λ` is a multiplicatively closed additive subgroup
  of a ring with `⋂ₖ q^k Λ = 0` and multiplication by `q` injective, then `x ∈ q Λ` and
  `(1 + x)^m = 1` with `m > 0` force `x = 0` (`eq_zero_of_one_add_pow_eq_one`).
* `localOrder A v`: the elements of `ℚ_v ⊗ A` whose left multiplication matrix in the basis
  `1 ⊗ b` (`b = Module.finBasis ℚ A`) has entries in `𝒪_v`. It is a subring, and
  `⋂ₖ q^k Λ_v = 0` (`eq_zero_of_forall_mem_powMul_localOrder`).
* `congruenceLevel σ v q`: the points `g` with `g - 1, g⁻¹ - 1 ∈ q Λ_v`. It is open
  (`isOpen_congruenceLevel`) and torsion-free (`congruenceLevel_torsionFree`).
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shimura.SmallLevels

open Finset

section Generic

variable {R : Type*} [Ring R]

/-- The additive subgroup `q^k Λ` of `R`. -/
def powMul (Λ : NonUnitalSubring R) (q k : ℕ) : AddSubgroup R :=
  Λ.toAddSubgroup.map (AddMonoidHom.mulLeft ((q : R) ^ k))

variable {Λ : NonUnitalSubring R} {q : ℕ}

theorem mem_powMul {k : ℕ} {x : R} :
    x ∈ powMul Λ q k ↔ ∃ y ∈ Λ, (q : R) ^ k * y = x :=
  Iff.rfl

theorem natCast_pow_mul_mem (j : ℕ) {y : R} (hy : y ∈ Λ) : (q : R) ^ j * y ∈ Λ := by
  rw [← Nat.cast_pow, ← nsmul_eq_mul]
  exact nsmul_mem hy _

theorem mem_of_mem_powMul {k : ℕ} {x : R} (hx : x ∈ powMul Λ q k) : x ∈ Λ := by
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  exact natCast_pow_mul_mem k hy

theorem powMul_mono {j k : ℕ} (h : j ≤ k) : powMul Λ q k ≤ powMul Λ q j := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  refine mem_powMul.2 ⟨(q : R) ^ (k - j) * y, natCast_pow_mul_mem _ hy, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem natCast_mul_mem_powMul {k : ℕ} {x : R} (hx : x ∈ powMul Λ q k) :
    (q : R) * x ∈ powMul Λ q (k + 1) := by
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  exact mem_powMul.2 ⟨y, hy, by rw [pow_succ', mul_assoc]⟩

theorem mul_mem_powMul_of_mem {k : ℕ} {x z : R} (hx : x ∈ powMul Λ q k) (hz : z ∈ Λ) :
    x * z ∈ powMul Λ q k := by
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  exact mem_powMul.2 ⟨y * z, mul_mem hy hz, (mul_assoc _ _ _).symm⟩

theorem natCast_mul_mem_powMul_of_mem {k : ℕ} (c : ℕ) {x : R} (hx : x ∈ powMul Λ q k) :
    (c : R) * x ∈ powMul Λ q k := by
  rw [← nsmul_eq_mul]
  exact AddSubgroup.nsmul_mem _ hx _

theorem mul_mem_powMul {j k : ℕ} {x x' : R} (hx : x ∈ powMul Λ q j)
    (hx' : x' ∈ powMul Λ q k) : x * x' ∈ powMul Λ q (j + k) := by
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_powMul.1 hx'
  refine mem_powMul.2 ⟨y * y', mul_mem hy hy', ?_⟩
  have hc : y * (q : R) ^ k = (q : R) ^ k * y := ((Nat.cast_commute q y).pow_left k).eq.symm
  rw [pow_add]
  simp only [mul_assoc]
  rw [← mul_assoc y, hc, mul_assoc]

theorem pow_succ_mem_powMul {k : ℕ} {x : R} (hx : x ∈ powMul Λ q k) :
    ∀ m : ℕ, x ^ (m + 1) ∈ powMul Λ q (k * (m + 1))
  | 0 => by simpa using hx
  | m + 1 => by
    rw [pow_succ, show k * (m + 1 + 1) = k * (m + 1) + k by ring]
    exact mul_mem_powMul (pow_succ_mem_powMul hx m) hx

/-- Cancellation of `q^k` when multiplication by `q` is injective. -/
theorem mem_powMul_of_natCast_pow_mul (htor : ∀ x : R, (q : R) * x = 0 → x = 0) {k j : ℕ}
    {u : R} (h : (q : R) ^ k * u ∈ powMul Λ q (k + j)) : u ∈ powMul Λ q j := by
  obtain ⟨z, hz, hzu⟩ := mem_powMul.1 h
  refine mem_powMul.2 ⟨z, hz, ?_⟩
  have h0 : (q : R) ^ k * ((q : R) ^ j * z - u) = 0 := by
    rw [mul_sub, ← mul_assoc, ← pow_add, hzu, sub_self]
  have hcancel : ∀ i : ℕ, ∀ w : R, (q : R) ^ i * w = 0 → w = 0 := by
    intro i
    induction i with
    | zero => intro w hw; simpa using hw
    | succ i ih =>
      intro w hw
      exact ih w (htor _ (by rw [← mul_assoc, ← pow_succ']; exact hw))
  exact sub_eq_zero.1 (hcancel k _ h0)

theorem one_add_pow_sub_one_mem {k : ℕ} {x : R} (hx : x ∈ powMul Λ q k) :
    ∀ n : ℕ, (1 + x) ^ n - 1 ∈ powMul Λ q k
  | 0 => by simp
  | n + 1 => by
    have e : (1 + x) ^ (n + 1) - 1 = ((1 + x) ^ n - 1) * (1 + x) + x := by
      rw [pow_succ]
      noncomm_ring
    have h := one_add_pow_sub_one_mem hx n
    rw [e, mul_add, mul_one]
    exact add_mem (add_mem h (mul_mem_powMul_of_mem h (mem_of_mem_powMul hx))) hx

/-- `(1 + x)^m ≡ 1 + m x` modulo `q^{2a} Λ` for `x ∈ q^a Λ`. -/
theorem one_add_pow_sub_mem {a : ℕ} {x : R} (hx : x ∈ powMul Λ q a) :
    ∀ m : ℕ, (1 + x) ^ m - 1 - (m : R) * x ∈ powMul Λ q (a + a)
  | 0 => by simp
  | m + 1 => by
    have h := one_add_pow_sub_mem hx m
    have e : (1 + x) ^ (m + 1) - 1 - ((m + 1 : ℕ) : R) * x =
        ((1 + x) ^ m - 1 - (m : R) * x) * (1 + x) + (m : R) * (x * x) := by
      rw [pow_succ]
      push_cast
      noncomm_ring
    rw [e, mul_add, mul_one]
    exact add_mem (add_mem h (mul_mem_powMul_of_mem h (mem_of_mem_powMul hx)))
      (natCast_mul_mem_powMul_of_mem m (mul_mem_powMul hx hx))

/-- For a prime `q`, `(1 + x)^q ≡ 1 + q x + x^q` modulo `q^{2a+1} Λ` for `x ∈ q^a Λ`. -/
theorem one_add_pow_prime_sub_mem (hq : q.Prime) {a : ℕ} {x : R} (hx : x ∈ powMul Λ q a) :
    (1 + x) ^ q - 1 - (q : R) * x - x ^ q ∈ powMul Λ q (a + a + 1) := by
  have hb := (Commute.one_right x).add_pow_prime_eq hq
  set S := ∑ k ∈ Ioo 0 q, x ^ (k - 1) * 1 ^ (q - k - 1) * ((q.choose k / q : ℕ) : R) with hS
  have h1 : (1 : ℕ) ∈ Ioo 0 q := mem_Ioo.2 ⟨Nat.one_pos, hq.one_lt⟩
  have hS1 : S = 1 + ∑ k ∈ (Ioo 0 q).erase 1,
      x ^ (k - 1) * 1 ^ (q - k - 1) * ((q.choose k / q : ℕ) : R) := by
    rw [hS, ← add_sum_erase _ _ h1]
    congr 1
    simp [Nat.div_self hq.pos]
  have hT : ∑ k ∈ (Ioo 0 q).erase 1,
      x ^ (k - 1) * 1 ^ (q - k - 1) * ((q.choose k / q : ℕ) : R) ∈ powMul Λ q a := by
    refine sum_mem fun k hk => ?_
    obtain ⟨hk1, hk⟩ := mem_erase.1 hk
    obtain ⟨hk0, -⟩ := mem_Ioo.1 hk
    obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 1 := ⟨k - 2, by omega⟩
    have hxk : x ^ (k - 1) ∈ powMul Λ q a := by
      rw [hj]
      exact powMul_mono (by nlinarith) (pow_succ_mem_powMul hx j)
    rw [one_pow, mul_one, ← Nat.cast_comm]
    exact natCast_mul_mem_powMul_of_mem _ hxk
  have e : (1 + x) ^ q - 1 - (q : R) * x - x ^ q =
      (q : R) * (x * ∑ k ∈ (Ioo 0 q).erase 1,
        x ^ (k - 1) * 1 ^ (q - k - 1) * ((q.choose k / q : ℕ) : R)) := by
    rw [add_comm (1 : R) x, hb, hS1, one_pow, mul_one]
    noncomm_ring
  rw [e]
  exact natCast_mul_mem_powMul (mul_mem_powMul hx hT)

/-- One step of the descent: if `x ∈ q^a Λ` with `a ≥ 1` and `(1 + x)^r = 1` for a prime `r`, then
`x ∈ q^{a+1} Λ`. For `r ≠ q` this uses `(1 + x)^r ≡ 1 + r x` and Bezout; for `r = q` it uses
`q ≥ 3`. -/
theorem mem_powMul_succ_of_pow_eq_one (htor : ∀ x : R, (q : R) * x = 0 → x = 0)
    (hq : q.Prime) (hq3 : 3 ≤ q) {r : ℕ} (hr : r.Prime) {a : ℕ} (ha : 1 ≤ a) {x : R}
    (hx : x ∈ powMul Λ q a) (h : (1 + x) ^ r = 1) : x ∈ powMul Λ q (a + 1) := by
  obtain ⟨y, hy, rfl⟩ := mem_powMul.1 hx
  suffices hy1 : y ∈ powMul Λ q 1 by
    obtain ⟨z, hz, rfl⟩ := mem_powMul.1 hy1
    exact mem_powMul.2 ⟨z, hz, by rw [pow_add, mul_assoc]⟩
  by_cases hrq : r = q
  · subst hrq
    have hE := one_add_pow_prime_sub_mem hq hx
    rw [h] at hE
    obtain ⟨j, hj⟩ : ∃ j, r = j + 1 := ⟨r - 1, by have := hr.one_lt; omega⟩
    have hxq : ((r : R) ^ a * y) ^ r ∈ powMul Λ r (a + 2) := by
      have := pow_succ_mem_powMul hx j
      rw [← hj] at this
      exact powMul_mono (by nlinarith) this
    have hqx : (r : R) * ((r : R) ^ a * y) ∈ powMul Λ r (a + 2) := by
      have e : (r : R) * ((r : R) ^ a * y) =
          -((1 : R) - 1 - (r : R) * ((r : R) ^ a * y) - ((r : R) ^ a * y) ^ r) -
            ((r : R) ^ a * y) ^ r := by
        abel
      rw [e]
      exact sub_mem (neg_mem (powMul_mono (by omega) hE)) hxq
    rw [← mul_assoc, ← pow_succ', show a + 2 = (a + 1) + 1 by omega] at hqx
    exact mem_powMul_of_natCast_pow_mul htor hqx
  · have hE := one_add_pow_sub_mem hx r
    rw [h] at hE
    have hrx : (q : R) ^ a * ((r : R) * y) ∈ powMul Λ q (a + 1) := by
      have e : (q : R) ^ a * ((r : R) * y) = -((1 : R) - 1 - (r : R) * ((q : R) ^ a * y)) := by
        rw [sub_self, zero_sub, neg_neg, ← mul_assoc, ← mul_assoc,
          ((Nat.cast_commute r (q : R)).pow_right a).eq]
      rw [e]
      exact neg_mem (powMul_mono (by omega) hE)
    have hry := mem_powMul_of_natCast_pow_mul htor hrx
    have hcop : IsCoprime (r : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hr hq).2 hrq)
    obtain ⟨u, w, huw⟩ := hcop
    have e : y = (u : R) * ((r : R) * y) + (w : R) * ((q : R) * y) := by
      have h1 : ((u * r + w * q : ℤ) : R) = 1 := by rw [huw, Int.cast_one]
      push_cast at h1
      rw [← mul_assoc, ← mul_assoc, ← add_mul, h1, one_mul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [← zsmul_eq_mul]
      exact AddSubgroup.zsmul_mem _ hry _
    · rw [← zsmul_eq_mul]
      exact AddSubgroup.zsmul_mem _ (mem_powMul.2 ⟨y, hy, by rw [pow_one]⟩) _

/-- **Torsion-freeness of `1 + q Λ`.** Let `q ≥ 3` be prime, multiplication by `q` injective on
`R`, and `Λ` a multiplicatively closed additive subgroup with `⋂ₖ q^k Λ = 0`. If `x ∈ q Λ` and
`(1 + x)^m = 1` for some `m > 0`, then `x = 0`. -/
theorem eq_zero_of_one_add_pow_eq_one (htor : ∀ x : R, (q : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k, x ∈ powMul Λ q k) → x = 0) (hq : q.Prime) (hq3 : 3 ≤ q) {x : R}
    (hx : x ∈ powMul Λ q 1) {m : ℕ} (hm : 0 < m) (h : (1 + x) ^ m = 1) : x = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using h
    have hr : m.minFac.Prime := Nat.minFac_prime hm1
    set m' := m / m.minFac
    have hmm' : m = m' * m.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd m)).symm
    have hm'pos : 0 < m' := Nat.div_pos (Nat.minFac_le hm) hr.pos
    have hm'lt : m' < m := Nat.div_lt_self hm hr.one_lt
    set x' := (1 + x) ^ m' - 1
    have hx' : x' ∈ powMul Λ q 1 := one_add_pow_sub_one_mem hx m'
    have hx'r : (1 + x') ^ m.minFac = 1 := by
      rw [show 1 + x' = (1 + x) ^ m' by simp [x'], ← pow_mul, ← hmm', h]
    have hall : ∀ k, x' ∈ powMul Λ q (k + 1) := by
      intro k
      induction k with
      | zero => exact hx'
      | succ k ihk =>
        exact mem_powMul_succ_of_pow_eq_one htor hq hq3 hr (by omega) ihk hx'r
    have hx'0 : x' = 0 := hsep x' fun k => powMul_mono (Nat.le_succ k) (hall k)
    exact ih m' hm'lt hm'pos (sub_eq_zero.1 hx'0)

/-- An element `g` of finite order with `g - 1 ∈ q Λ` is `1`, under the hypotheses of
`eq_zero_of_one_add_pow_eq_one`. -/
theorem eq_one_of_isOfFinOrder (htor : ∀ x : R, (q : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k, x ∈ powMul Λ q k) → x = 0) (hq : q.Prime) (hq3 : 3 ≤ q) {g : R}
    (hg : g - 1 ∈ powMul Λ q 1) (hfin : IsOfFinOrder g) : g = 1 := by
  obtain ⟨m, hm, hgm⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have := eq_zero_of_one_add_pow_eq_one htor hsep hq hq3 hg hm (by rwa [add_sub_cancel])
  exact sub_eq_zero.1 this

/-- `1 + q Λ` is closed under multiplication. -/
theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ powMul Λ q 1) (hb : b - 1 ∈ powMul Λ q 1) :
    a * b - 1 ∈ powMul Λ q 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [e]
  exact add_mem (add_mem (mul_mem_powMul_of_mem ha (mem_of_mem_powMul hb)) ha) hb

end Generic

section MatrixSubring

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [CommRing S]

/-- Matrices with entries in a subring `O`. -/
def matrixSubring (O : Subring S) : Subring (Matrix ι ι S) where
  carrier := {M | ∀ i j, M i j ∈ O}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq] at hM hN ⊢
    intro i j
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq] at hM hN ⊢
    exact fun i j => add_mem (hM i j) (hN i j)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact fun _ _ => zero_mem _
  neg_mem' {M} hM := by
    simp only [Set.mem_ofPred_eq] at hM ⊢
    exact fun i j => neg_mem (hM i j)

theorem mem_matrixSubring {O : Subring S} {M : Matrix ι ι S} :
    M ∈ (matrixSubring O : Subring (Matrix ι ι S)) ↔ ∀ i j, M i j ∈ O :=
  Iff.rfl

end MatrixSubring

section Local

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Langlands.Global
open scoped NumberField TensorProduct

variable (A : Type*) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]

/-- The basis `1 ⊗ b` of `ℚ_v ⊗ A`, for the chosen basis `b` of `A`. -/
abbrev localBasis (v : FinitePlace ℚ) :
    Module.Basis (Fin (Module.finrank ℚ A)) (FiniteCompletion ℚ v) (FiniteCompletion ℚ v ⊗[ℚ] A) :=
  Algebra.TensorProduct.basis (FiniteCompletion ℚ v) (Module.finBasis ℚ A)

/-- The elements of `ℚ_v ⊗ A` whose left multiplication matrix in `localBasis` is integral. -/
def localOrder (v : FinitePlace ℚ) : Subring (FiniteCompletion ℚ v ⊗[ℚ] A) :=
  (matrixSubring (v.adicCompletionIntegers ℚ).toSubring).comap
    (Algebra.leftMulMatrix (localBasis A v)).toRingHom

variable {A}

theorem mem_localOrder {v : FinitePlace ℚ} {x : FiniteCompletion ℚ v ⊗[ℚ] A} :
    x ∈ localOrder A v ↔
      ∀ i j, Algebra.leftMulMatrix (localBasis A v) x i j ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- A prime contained in `v` has valuation `< 1` in `ℚ_v`. -/
theorem valued_natCast_lt_one {q : ℕ} {v : FinitePlace ℚ} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v (q : FiniteCompletion ℚ v) < 1 := by
  have h : (q : FiniteCompletion ℚ v) = algebraMap (𝓞 ℚ) (FiniteCompletion ℚ v) (q : 𝓞 ℚ) :=
    (map_natCast _ q).symm
  rw [h]
  exact (valuedAdicCompletion_eq_valuation (K := ℚ) (v := v) (q : 𝓞 ℚ)).trans_lt
    ((valuation_lt_one_iff_mem (v := v) (K := ℚ) (q : 𝓞 ℚ)).2 hv)

omit [Module.Finite ℚ A] in
/-- Multiplication by a nonzero natural number is injective on `ℚ_v ⊗ A`. -/
theorem natCast_mul_eq_zero {v : FinitePlace ℚ} {q : ℕ} (hq : q ≠ 0)
    (x : FiniteCompletion ℚ v ⊗[ℚ] A) (hx : (q : FiniteCompletion ℚ v ⊗[ℚ] A) * x = 0) :
    x = 0 := by
  have hu : IsUnit (q : FiniteCompletion ℚ v ⊗[ℚ] A) := by
    have : IsUnit (q : ℚ) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hq)
    simpa using this.map (algebraMap ℚ (FiniteCompletion ℚ v ⊗[ℚ] A))
  exact hu.mul_right_eq_zero.1 hx

/-- `⋂ₖ q^k Λ_v = 0` for a prime `q` contained in `v`. -/
theorem eq_zero_of_forall_mem_powMul_localOrder {v : FinitePlace ℚ} {q : ℕ}
    (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) (x : FiniteCompletion ℚ v ⊗[ℚ] A)
    (hx : ∀ k, x ∈ powMul (localOrder A v).toNonUnitalSubring q k) : x = 0 := by
  apply Algebra.leftMulMatrix_injective (localBasis A v)
  rw [map_zero]
  ext i j
  rw [Matrix.zero_apply]
  by_contra hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valued_natCast_lt_one hv)
    (Units.mk0 _ ((Valued.v).ne_zero_iff.2 hne))
  obtain ⟨y, hy, hxy⟩ := mem_powMul.1 (hx n)
  have hentry : Algebra.leftMulMatrix (localBasis A v) x i j =
      (q : FiniteCompletion ℚ v) ^ n * Algebra.leftMulMatrix (localBasis A v) y i j := by
    have e : (q : FiniteCompletion ℚ v ⊗[ℚ] A) ^ n * y = ((q : FiniteCompletion ℚ v) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [← hxy, e, map_smul, Matrix.smul_apply, smul_eq_mul]
  have hy' : Valued.v (Algebra.leftMulMatrix (localBasis A v) y i j) ≤ 1 := hy i j
  have hle : Valued.v (Algebra.leftMulMatrix (localBasis A v) x i j) ≤
      Valued.v (q : FiniteCompletion ℚ v) ^ n := by
    rw [hentry, map_mul, map_pow]
    exact mul_le_of_le_one_right' hy'
  exact lt_irrefl _ (hle.trans_lt hn)

end Local

section Level

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Langlands.Global
open scoped NumberField TensorProduct

variable {A : Type*} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (σ : AlgebraInvolution ℚ A)

/-- The principal congruence level modulo `q` of `σ(ℚ_v)`: the points `g` with `g - 1` and
`g⁻¹ - 1` in `q Λ_v`. -/
def congruenceLevel (v : FinitePlace ℚ) (q : ℕ) : Subgroup (σ.Points (FiniteCompletion ℚ v)) where
  carrier := {g | ((g.1.1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈
        powMul (localOrder A v).toNonUnitalSubring q 1 ∧
      (((g.1.1)⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈
        powMul (localOrder A v).toNonUnitalSubring q 1}
  one_mem' := by
    change ((1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _ ∧
      (((1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ)⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) :
        FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _
    rw [inv_one, Units.val_one, sub_self]
    exact ⟨zero_mem _, zero_mem _⟩
  mul_mem' {g h} hg hh := by
    change ((g.1.1 * h.1.1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _ ∧
      (((g.1.1 * h.1.1)⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    exact ⟨mul_sub_one_mem hg.1 hh.1, mul_sub_one_mem hh.2 hg.2⟩
  inv_mem' {g} hg := by
    change (((g.1.1)⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _ ∧
      (((g.1.1)⁻¹⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) - 1 ∈ _
    rw [inv_inv]
    exact ⟨hg.2, hg.1⟩

/-- The principal congruence level is open. -/
theorem isOpen_congruenceLevel (v : FinitePlace ℚ) {q : ℕ} (hq : q ≠ 0) :
    IsOpen (congruenceLevel σ v q : Set (σ.Points (FiniteCompletion ℚ v))) := by
  let : TopologicalSpace (FiniteCompletion ℚ v ⊗[ℚ] A) :=
    moduleTopology (FiniteCompletion ℚ v) (FiniteCompletion ℚ v ⊗[ℚ] A)
  have : IsTopologicalRing (FiniteCompletion ℚ v ⊗[ℚ] A) :=
    IsModuleTopology.isTopologicalRing (FiniteCompletion ℚ v) _
  have hΛ : IsOpen (localOrder A v : Set (FiniteCompletion ℚ v ⊗[ℚ] A)) := by
    have hL : Continuous (Algebra.leftMulMatrix (localBasis A v)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (localBasis A v)).toLinearMap
    have hO : IsOpen {M : Matrix (Fin (Module.finrank ℚ A)) (Fin (Module.finrank ℚ A))
        (FiniteCompletion ℚ v) | ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (Valued.isOpen_valuationSubring _).preimage ((continuous_apply j).comp (continuous_apply i))
    exact hO.preimage hL
  set c : FiniteCompletion ℚ v ⊗[ℚ] A := algebraMap (FiniteCompletion ℚ v) _ ((q : FiniteCompletion ℚ v)⁻¹)
  have hq0 : (q : FiniteCompletion ℚ v) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (FiniteCompletion ℚ v))]
    exact (map_ne_zero_iff _ (algebraMap ℚ _).injective).2 (Nat.cast_ne_zero.2 hq)
  have hcq : c * (q : FiniteCompletion ℚ v ⊗[ℚ] A) = 1 := by
    rw [← map_natCast (algebraMap (FiniteCompletion ℚ v) (FiniteCompletion ℚ v ⊗[ℚ] A)), ← map_mul,
      inv_mul_cancel₀ hq0, map_one]
  have hU : IsOpen {b : FiniteCompletion ℚ v ⊗[ℚ] A |
      b - 1 ∈ powMul (localOrder A v).toNonUnitalSubring q 1} := by
    have e : {b : FiniteCompletion ℚ v ⊗[ℚ] A |
        b - 1 ∈ powMul (localOrder A v).toNonUnitalSubring q 1} =
        (fun b => c * (b - 1)) ⁻¹' (localOrder A v : Set (FiniteCompletion ℚ v ⊗[ℚ] A)) := by
      ext b
      constructor
      · intro hb
        obtain ⟨y, hy, hyb⟩ := mem_powMul.1 hb
        change c * (b - 1) ∈ localOrder A v
        rw [← hyb, pow_one, ← mul_assoc, hcq, one_mul]
        exact hy
      · intro hb
        refine mem_powMul.2 ⟨c * (b - 1), hb, ?_⟩
        have hqc : (q : FiniteCompletion ℚ v ⊗[ℚ] A) * c = 1 := (Nat.cast_commute q c).eq.trans hcq
        rw [pow_one, ← mul_assoc, hqc, one_mul]
    rw [e]
    exact hΛ.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have h1 : Continuous fun g : σ.Points (FiniteCompletion ℚ v) =>
      ((g.1.1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have h2 : Continuous fun g : σ.Points (FiniteCompletion ℚ v) =>
      (((g.1.1)⁻¹ : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  exact (hU.preimage h1).inter (hU.preimage h2)

/-- **Torsion-freeness.** For a prime `q ≥ 3` contained in `v` and a nonzero algebra `A`, the
only element of finite order of the principal congruence level modulo `q` is `1`. -/
theorem congruenceLevel_torsionFree [Nontrivial A] {v : FinitePlace ℚ} {q : ℕ} (hq : q.Prime)
    (hq3 : 3 ≤ q) (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) (g : σ.Points (FiniteCompletion ℚ v))
    (hg : g ∈ congruenceLevel σ v q) (hfin : IsOfFinOrder g) : g = 1 := by
  let f : σ.Points (FiniteCompletion ℚ v) →* FiniteCompletion ℚ v ⊗[ℚ] A :=
    (Units.coeHom _).comp ((MonoidHom.fst _ _).comp
      (σ.baseChange (FiniteCompletion ℚ v)).similitudes.subtype)
  have h1 : ((g.1.1 : (FiniteCompletion ℚ v ⊗[ℚ] A)ˣ) : FiniteCompletion ℚ v ⊗[ℚ] A) = 1 :=
    eq_one_of_isOfFinOrder (natCast_mul_eq_zero hq.ne_zero)
      (eq_zero_of_forall_mem_powMul_localOrder hv) hq hq3 hg.1 (f.isOfFinOrder hfin)
  have : Nontrivial (FiniteCompletion ℚ v ⊗[ℚ] A) :=
    (Algebra.TensorProduct.includeRight_injective (A := FiniteCompletion ℚ v) (B := A)
      (algebraMap ℚ (FiniteCompletion ℚ v)).injective).nontrivial
  have hmem := ((σ.baseChange (FiniteCompletion ℚ v)).mem_similitudes_iff g.1).1 g.2
  rw [h1, AlgebraInvolution.apply_one, one_mul] at hmem
  have hc : ((g.1.2 : (FiniteCompletion ℚ v)ˣ) : FiniteCompletion ℚ v) = 1 :=
    (algebraMap (FiniteCompletion ℚ v) (FiniteCompletion ℚ v ⊗[ℚ] A)).injective
      (by rw [← hmem, map_one])
  exact Subtype.ext (Prod.ext (Units.ext h1) (Units.ext hc))

/-- For a prime `q ≥ 3` contained in `v`, `σ(ℚ_v)` has an open subgroup whose only element of
finite order is `1`. -/
theorem exists_isOpen_torsionFree [Nontrivial A] {v : FinitePlace ℚ} {q : ℕ} (hq : q.Prime)
    (hq3 : 3 ≤ q) (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ W : Subgroup (σ.Points (FiniteCompletion ℚ v)),
      IsOpen (W : Set (σ.Points (FiniteCompletion ℚ v))) ∧ ∀ g ∈ W, IsOfFinOrder g → g = 1 :=
  ⟨congruenceLevel σ v q, isOpen_congruenceLevel σ v hq.ne_zero,
    congruenceLevel_torsionFree σ hq hq3 hv⟩

end Level

end Langlands.Shimura.SmallLevels
