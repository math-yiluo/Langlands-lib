import Mathlib

/-!
# Finite intersections of valuation subrings

Let `K` be a field, let `V i` (`i : ι`, `ι` finite) be valuation subrings of `K`, and let
`A ⊆ K` be a subring with `A = ⋂ i, V i`.  Following Matsumura, *Commutative Ring Theory*,
Theorem 12.2, we prove:

* every `V i` is the localization of `A` at the prime ideal `prime V hA i` cut out by the
  maximal ideal of `V i` (`isLocalization_atPrime`, `isLocalization_atPrime_valuationSubring`);
* if `ι` is nonempty, every maximal ideal of `A` is one of these primes
  (`exists_eq_prime_of_isMaximal`, `exists_isLocalization_atPrime_of_isMaximal`);
* `K` is the fraction field of `A` (`isFractionRing`).

The proof uses the geometric-sum trick: for `x : K` choose a prime `p` such that
`f = 1 + x + ⋯ + x ^ (p - 1)` is a unit of every `V i` containing `x`; then `f⁻¹` and `x * f⁻¹`
lie in every `V i`.
-/

namespace Langlands.CommutativeAlgebra.ValuationSubringIntersection

open Finset

universe u v w

/-- In a nontrivial commutative ring, at most one prime `p` makes the geometric sum
`∑_{n < p} a ^ n` vanish. -/
theorem prime_eq_of_geomSum_eq_zero {k : Type*} [CommRing k] [Nontrivial k] (a : k) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpa : ∑ n ∈ range p, a ^ n = 0)
    (hqa : ∑ n ∈ range q, a ^ n = 0) : p = q := by
  by_contra hne
  have hap : a ^ p = 1 := by
    have h := geom_sum_mul a p
    rw [hpa, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have haq : a ^ q = 1 := by
    have h := geom_sum_mul a q
    rw [hqa, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hne
  have ha : a = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hap, haq⟩
  subst ha
  rw [one_geom_sum] at hpa hqa
  have h1 : ringChar k ∣ p := (ringChar.spec k p).1 hpa
  have h2 : ringChar k ∣ q := (ringChar.spec k q).1 hqa
  have h3 : ringChar k ∣ Nat.gcd p q := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact CharP.ringChar_ne_one (Nat.dvd_one.1 h3)

variable {K : Type u} [Field K]

/-- For `x` in a valuation subring `W`, at most one prime `p` makes `∑_{n < p} x ^ n` a non-unit
of `W`. -/
theorem geomSum_valuation_lt_one_subsingleton (W : ValuationSubring K) (x : K) (hx : x ∈ W) :
    {p : ℕ | p.Prime ∧ W.valuation (∑ n ∈ range p, x ^ n) < 1}.Subsingleton := by
  rintro p ⟨hp, hpv⟩ q ⟨hq, hqv⟩
  let y : W := ⟨x, hx⟩
  have key : ∀ r : ℕ, W.valuation (∑ n ∈ range r, x ^ n) < 1 →
      ∑ n ∈ range r, (IsLocalRing.residue W y) ^ n = 0 := by
    intro r hr
    have hcoe : ((∑ n ∈ range r, y ^ n : W) : K) = ∑ n ∈ range r, x ^ n := by
      push_cast
      rfl
    rw [← hcoe, ← W.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff] at hr
    simpa [map_sum, map_pow] using hr
  exact prime_eq_of_geomSum_eq_zero _ hp hq (key p hpv) (key q hqv)

variable {ι : Type v} (V : ι → ValuationSubring K)

/-- For finitely many valuation subrings and any `x : K`, some prime `p` makes
`∑_{n < p} x ^ n` a unit of every `V i` that contains `x`. -/
theorem exists_prime_geomSum_valuation_eq_one [Finite ι] (x : K) :
    ∃ p : ℕ, p.Prime ∧ ∀ i, x ∈ V i → (V i).valuation (∑ n ∈ range p, x ^ n) = 1 := by
  let bad : ι → Set ℕ := fun i =>
    {p : ℕ | p.Prime ∧ x ∈ V i ∧ (V i).valuation (∑ n ∈ range p, x ^ n) < 1}
  have hfin : (⋃ i, bad i).Finite := Set.finite_iUnion fun i => by
    by_cases hx : x ∈ V i
    · exact (geomSum_valuation_lt_one_subsingleton (V i) x hx).finite.subset
        (fun p hp => ⟨hp.1, hp.2.2⟩)
    · exact Set.finite_empty.subset (fun p hp => (hx hp.2.1).elim)
  obtain ⟨p, hp, hpbad⟩ := (Nat.infinite_setOfPred_prime.sdiff hfin).nonempty
  refine ⟨p, hp, fun i hx => ?_⟩
  have hle : (V i).valuation (∑ n ∈ range p, x ^ n) ≤ 1 :=
    ((V i).valuation_le_one_iff _).2 (sum_mem fun n _ => pow_mem hx n)
  exact le_antisymm hle (not_lt.1 fun hlt => hpbad (Set.mem_iUnion.2 ⟨i, hp, hx, hlt⟩))

/-- The geometric-sum trick: for every `x : K` there is `s : K` such that `s` and `x * s` lie
in every `V i`, `s` is a unit of every `V i` containing `x`, and `s ≠ 0` as soon as there is at
least one valuation subring. -/
theorem exists_mem_mul_mem [Finite ι] (x : K) :
    ∃ s : K, (∀ i, s ∈ V i) ∧ (∀ i, x * s ∈ V i) ∧
      (∀ i, x ∈ V i → (V i).valuation s = 1) ∧ (Nonempty ι → s ≠ 0) := by
  obtain ⟨p, hp, hpv⟩ := exists_prime_geomSum_valuation_eq_one V x
  set f : K := ∑ n ∈ range p, x ^ n with hf_def
  have hbound : ∀ i, 1 ≤ (V i).valuation f ∧ (V i).valuation x ≤ (V i).valuation f := by
    intro i
    by_cases hx : x ∈ V i
    · rw [hpv i hx]
      exact ⟨le_rfl, ((V i).valuation_le_one_iff x).2 hx⟩
    · have hvx : 1 < (V i).valuation x := by
        rw [← not_le, (V i).valuation_le_one_iff]
        exact hx
      have hvx0 : (V i).valuation x ≠ 0 := (zero_lt_one.trans hvx).ne'
      have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
      have hsub1 : (V i).valuation (x - 1) = (V i).valuation x :=
        Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact hvx)
      have hpow : 1 < (V i).valuation (x ^ p) := by
        rw [map_pow]
        exact one_lt_pow₀ hvx hp.ne_zero
      have hsubp : (V i).valuation (x ^ p - 1) = (V i).valuation (x ^ p) :=
        Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact hpow)
      have hmul := congrArg (V i).valuation (geom_sum_mul x p)
      rw [← hf_def, map_mul, hsub1, hsubp, hp1, pow_succ, map_mul, map_pow] at hmul
      have hfeq : (V i).valuation f = (V i).valuation x ^ (p - 1) := mul_right_cancel₀ hvx0 hmul
      have hpm1 : p - 1 ≠ 0 := by have := hp.two_le; omega
      have hle : (V i).valuation x ≤ (V i).valuation f :=
        hfeq ▸ le_self_pow₀ hvx.le hpm1
      exact ⟨hvx.le.trans hle, hle⟩
  have hf0 : ∀ i, (V i).valuation f ≠ 0 := fun i => (zero_lt_one.trans_le (hbound i).1).ne'
  have hfpos : ∀ i, 0 < (V i).valuation f := fun i => zero_lt_iff.2 (hf0 i)
  refine ⟨f⁻¹, fun i => ?_, fun i => ?_, fun i hx => ?_, fun ⟨i⟩ => ?_⟩
  · rw [← (V i).valuation_le_one_iff, ← one_div, map_div₀, map_one, div_le_one₀ (hfpos i)]
    exact (hbound i).1
  · rw [← (V i).valuation_le_one_iff, ← div_eq_mul_inv, map_div₀, div_le_one₀ (hfpos i)]
    exact (hbound i).2
  · rw [map_inv₀, hpv i hx, inv_one]
  · exact inv_ne_zero fun h => hf0 i (by rw [h, map_zero])

variable {A : Subring K} (hA : ∀ x, x ∈ A ↔ ∀ i, x ∈ V i)
include hA

/-- The inclusion of the intersection `A` into `V i`. -/
def toValuationSubring (i : ι) : A →+* V i :=
  A.subtype.codRestrict (V i) fun a => (hA a).1 a.2 i

@[simp]
theorem coe_toValuationSubring (i : ι) (a : A) :
    ((toValuationSubring V hA i a : V i) : K) = a := rfl

/-- The prime ideal of `A` obtained by contracting the maximal ideal of `V i`. -/
def prime (i : ι) : Ideal A :=
  (IsLocalRing.maximalIdeal (V i)).comap (toValuationSubring V hA i)

instance prime_isPrime (i : ι) : (prime V hA i).IsPrime := by
  unfold prime
  infer_instance

theorem mem_prime (i : ι) (a : A) : a ∈ prime V hA i ↔ (V i).valuation (a : K) < 1 := by
  rw [prime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem not_mem_prime (i : ι) (a : A) : a ∉ prime V hA i ↔ (V i).valuation (a : K) = 1 := by
  rw [mem_prime, not_lt]
  exact ⟨fun h => le_antisymm (((V i).valuation_le_one_iff _).2 ((hA a).1 a.2 i)) h,
    fun h => h.ge⟩

/-- **Localization.** If `S` is an `A`-algebra embedded into `K` compatibly with `A ⊆ K`, with
image exactly `V i`, then `S` is the localization of `A` at `prime V hA i`. -/
theorem isLocalization_atPrime [Finite ι] (i : ι) {S : Type w} [CommRing S] [Algebra A S]
    (j : S →+* K) (hj : Function.Injective j) (hjA : ∀ a : A, j (algebraMap A S a) = a)
    (hrange : ∀ y : K, y ∈ V i ↔ ∃ s, j s = y) :
    IsLocalization.AtPrime S (prime V hA i) := by
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    have hv : (V i).valuation (a : K) = 1 := (not_mem_prime V hA i a).1 ha
    have ha0 : (a : K) ≠ 0 := fun h => by simp [h] at hv
    have hinv : (a : K)⁻¹ ∈ V i := by
      rw [← (V i).valuation_le_one_iff, map_inv₀, hv, inv_one]
    obtain ⟨t, ht⟩ := (hrange _).1 hinv
    refine IsUnit.of_mul_eq_one t (hj ?_)
    rw [map_mul, hjA, ht, map_one, mul_inv_cancel₀ ha0]
  · intro z
    have hz : j z ∈ V i := (hrange _).2 ⟨z, rfl⟩
    obtain ⟨s, hs, hxs, hv, -⟩ := exists_mem_mul_mem V (j z)
    refine ⟨(⟨j z * s, (hA _).2 hxs⟩, ⟨⟨s, (hA _).2 hs⟩, ?_⟩), hj ?_⟩
    · rw [Ideal.mem_primeCompl_iff, not_mem_prime]
      exact hv i hz
    · rw [map_mul, hjA, hjA]
  · intro a b hab
    refine ⟨1, ?_⟩
    have h : (a : K) = b := by rw [← hjA, ← hjA, hab]
    rw [Subtype.ext h]

/-- `V i` itself, as an `A`-algebra through `toValuationSubring`, is the localization of `A` at
`prime V hA i`. -/
theorem isLocalization_atPrime_valuationSubring [Finite ι] (i : ι) :
    letI := (toValuationSubring V hA i).toAlgebra
    IsLocalization.AtPrime (V i) (prime V hA i) := by
  let := (toValuationSubring V hA i).toAlgebra
  exact isLocalization_atPrime V hA i (V i).subtype (V i).subtype_injective (fun _ => rfl)
    fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩

/-- **Maximal ideals.** If `ι` is nonempty, every maximal ideal of `A` is one of the primes
`prime V hA i`. -/
theorem exists_eq_prime_of_isMaximal [Finite ι] [Nonempty ι] (M : Ideal A) [hM : M.IsMaximal] :
    ∃ i, M = prime V hA i := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsub : (M : Set A) ⊆ ⋃ i ∈ (Set.univ : Set ι), (prime V hA i : Set A) := by
    intro a ha
    by_contra hcon
    simp only [Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
      not_exists] at hcon
    have hv : ∀ i, (V i).valuation (a : K) = 1 := fun i => (not_mem_prime V hA i a).1 (hcon i)
    have ha0 : (a : K) ≠ 0 := fun h => by simpa [h] using hv i₀
    have hinv : (a : K)⁻¹ ∈ A := (hA _).2 fun i => by
      rw [← (V i).valuation_le_one_iff, map_inv₀, hv i, inv_one]
    have hunit : IsUnit a := IsUnit.of_mul_eq_one ⟨(a : K)⁻¹, hinv⟩
      (Subtype.ext (mul_inv_cancel₀ ha0))
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M ha hunit)
  obtain ⟨i, -, hi⟩ :=
    (Ideal.subset_union_prime_finite Set.finite_univ i₀ i₀
      (fun i _ _ _ => prime_isPrime V hA i)).1 hsub
  exact ⟨i, hM.eq_of_le (prime_isPrime V hA i).ne_top hi⟩

/-- **Localizations at maximal ideals.** Given, for every `i`, a ring `S i` with a ring map
`κ i : A →+* S i` and an embedding `j i : S i →+* K` onto `V i` compatible with `A ⊆ K`, every
maximal ideal `M` of `A` has some `S i` as its localization (for the algebra structure `κ i`). -/
theorem exists_isLocalization_atPrime_of_isMaximal [Finite ι] [Nonempty ι] (M : Ideal A)
    [M.IsMaximal] {S : ι → Type w} [∀ i, CommRing (S i)] (κ : ∀ i, A →+* S i)
    (j : ∀ i, S i →+* K) (hj : ∀ i, Function.Injective (j i))
    (hjκ : ∀ i (a : A), j i (κ i a) = a) (hrange : ∀ i (y : K), y ∈ V i ↔ ∃ s, j i s = y) :
    ∃ i, letI := (κ i).toAlgebra
      IsLocalization.AtPrime (S i) M := by
  obtain ⟨i, rfl⟩ := exists_eq_prime_of_isMaximal V hA M
  let := (κ i).toAlgebra
  exact ⟨i, isLocalization_atPrime V hA i (j i) (hj i) (hjκ i) (hrange i)⟩

/-- **Fraction field.** `K` is the fraction field of `A`. -/
theorem isFractionRing [Finite ι] : IsFractionRing A K := by
  refine IsFractionRing.of_field A K fun z => ?_
  by_cases hz : z ∈ A
  · exact ⟨⟨z, hz⟩, 1, by rw [map_one, div_one]; rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, z ∉ V i := not_forall.1 fun h => hz ((hA z).2 h)
    obtain ⟨s, hs, hzs, -, hs0⟩ := exists_mem_mul_mem V z
    have hs0 := hs0 ⟨i⟩
    refine ⟨⟨z * s, (hA _).2 hzs⟩, ⟨s, (hA _).2 hs⟩, ?_⟩
    change z = z * s / s
    rw [mul_div_assoc, div_self hs0, mul_one]

omit hA

/-- Two distinct valuation subrings of Krull dimension at most one (for instance discrete
valuation rings), the second of which is not all of `K`, are incomparable. -/
theorem not_le_of_ne {W W' : ValuationSubring K} [Ring.KrullDimLE 1 W] (hne : W ≠ W')
    (htop : W' ≠ ⊤) : ¬ W ≤ W' := fun hle =>
  (ValuationSubring.eq_self_or_eq_top_of_le hle).elim hne htop

end Langlands.CommutativeAlgebra.ValuationSubringIntersection
