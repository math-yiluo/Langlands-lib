import Langlands.Algebra.FiniteOrderCongruenceStatement
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# Finite-order detection modulo an integer: proof

We prove `Langlands.FiniteOrderCongruenceDetectionStatement`.

* For an additive commutative group `F`, `fil F p k` is the additive subgroup of the endomorphism
  ring `AddMonoid.End F` consisting of the endomorphisms with image in `p ^ k F`.
* If `F` is torsion-free and finitely generated, `p` is prime, `1 ≤ a` and `3 ≤ p ∨ 2 ≤ a`, then
  an endomorphism `g` of finite order with `g - 1 ∈ fil F p a` is `1`
  (`eq_one_of_sub_one_mem_fil`).
* For the target, `σ` is restricted to the torsion-free subgroup `n M`, where it is congruent to
  the identity modulo `p ^ a`, with `p ^ a ∣ n`. Hence `σ` fixes `n M`, so `σ x - x` is a torsion
  element of `n M`, hence zero.
-/

universe u

set_option autoImplicit false

namespace Langlands.FiniteOrderCongruence

section Filtration

variable {F : Type*} [AddCommGroup F]

theorem end_mul_apply (x y : AddMonoid.End F) (v : F) : (x * y) v = x (y v) := rfl

theorem end_add_apply (x y : AddMonoid.End F) (v : F) : (x + y) v = x v + y v := rfl

theorem end_sub_apply (x y : AddMonoid.End F) (v : F) : (x - y) v = x v - y v := rfl

theorem end_neg_apply (x : AddMonoid.End F) (v : F) : (-x) v = -x v := rfl

variable (F) in
/-- The endomorphisms of `F` with image in `p ^ k F`. -/
def fil (p k : ℕ) : AddSubgroup (AddMonoid.End F) where
  carrier := {x | ∀ v, ∃ w, x v = (p ^ k) • w}
  zero_mem' := fun _ => ⟨0, by rw [smul_zero]; rfl⟩
  add_mem' := by
    intro x y hx hy v
    obtain ⟨w₁, h₁⟩ := hx v
    obtain ⟨w₂, h₂⟩ := hy v
    exact ⟨w₁ + w₂, by rw [end_add_apply, h₁, h₂, smul_add]⟩
  neg_mem' := by
    intro x hx v
    obtain ⟨w, h⟩ := hx v
    exact ⟨-w, by rw [end_neg_apply, h, smul_neg]⟩

variable {p : ℕ}

theorem mem_fil {k : ℕ} {x : AddMonoid.End F} : x ∈ fil F p k ↔ ∀ v, ∃ w, x v = (p ^ k) • w :=
  Iff.rfl

theorem fil_mono {j k : ℕ} (h : j ≤ k) : fil F p k ≤ fil F p j := by
  intro x hx v
  obtain ⟨w, hw⟩ := hx v
  refine ⟨(p ^ (k - j)) • w, ?_⟩
  rw [hw, smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem mul_mem_fil {j k : ℕ} {x y : AddMonoid.End F} (hx : x ∈ fil F p j)
    (hy : y ∈ fil F p k) : x * y ∈ fil F p (j + k) := by
  intro v
  obtain ⟨w, hw⟩ := hy v
  obtain ⟨w', hw'⟩ := hx w
  refine ⟨w', ?_⟩
  rw [end_mul_apply, hw, map_nsmul, hw', smul_smul, ← pow_add, add_comm k j]

theorem mul_mem_fil_left {k : ℕ} {x : AddMonoid.End F} (y : AddMonoid.End F)
    (hx : x ∈ fil F p k) : y * x ∈ fil F p k := by
  intro v
  obtain ⟨w, hw⟩ := hx v
  exact ⟨y w, by rw [end_mul_apply, hw, map_nsmul]⟩

theorem mul_mem_fil_right {k : ℕ} {x : AddMonoid.End F} (y : AddMonoid.End F)
    (hx : x ∈ fil F p k) : x * y ∈ fil F p k := by
  intro v
  exact hx (y v)

theorem natCast_mul_mem_fil {k : ℕ} (c : ℕ) {x : AddMonoid.End F} (hx : x ∈ fil F p k) :
    (c : AddMonoid.End F) * x ∈ fil F p k :=
  mul_mem_fil_left _ hx

theorem prime_mul_mem_fil {k : ℕ} {x : AddMonoid.End F} (hx : x ∈ fil F p k) :
    (p : AddMonoid.End F) * x ∈ fil F p (k + 1) := by
  intro v
  obtain ⟨w, hw⟩ := hx v
  refine ⟨w, ?_⟩
  rw [end_mul_apply, AddMonoid.End.natCast_apply, hw, smul_smul, ← pow_succ']

theorem pow_mem_fil {a : ℕ} {x : AddMonoid.End F} (hx : x ∈ fil F p a) :
    ∀ i : ℕ, x ^ i ∈ fil F p (a * i)
  | 0 => by
    intro v
    refine ⟨v, ?_⟩
    rw [pow_zero, mul_zero, pow_zero, one_smul]
    rfl
  | i + 1 => by
    rw [pow_succ, mul_add, mul_one]
    exact mul_mem_fil (pow_mem_fil hx i) hx

/-- Division by `p` in a torsion-free group. -/
theorem mem_fil_of_prime_mul_mem [IsAddTorsionFree F] (hp : p ≠ 0) {k : ℕ}
    {x : AddMonoid.End F} (h : (p : AddMonoid.End F) * x ∈ fil F p (k + 1)) :
    x ∈ fil F p k := by
  intro v
  obtain ⟨w, hw⟩ := h v
  refine ⟨w, nsmul_right_injective hp ?_⟩
  change p • x v = p • ((p ^ k) • w)
  rw [smul_smul, ← pow_succ', ← hw]
  rfl

/-- Krull's intersection theorem: an endomorphism with image in every `p ^ k F` is zero. -/
theorem eq_zero_of_forall_mem_fil [IsAddTorsionFree F] [Module.Finite ℤ F] (hp : p.Prime)
    {x : AddMonoid.End F} (hx : ∀ k, x ∈ fil F p k) : x = 0 := by
  have hI : Ideal.span {(p : ℤ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]
    have := hp.two_le
    omega
  have key := Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree (M := F) _ hI
  ext v
  rw [AddMonoid.End.zero_apply]
  have hmem : x v ∈ (⨅ i : ℕ, (Ideal.span {(p : ℤ)}) ^ i • ⊤ : Submodule ℤ F) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨w, hw⟩ := hx i v
    rw [hw, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_pow]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) i)
      Submodule.mem_top
  rw [key] at hmem
  exact (Submodule.mem_bot ℤ).1 hmem

/-- The second-order binomial congruence
`(1 + x) ^ m ≡ 1 + m x + C(m, 2) x ^ 2` modulo `fil F p (3 a)` for `x ∈ fil F p a`. -/
theorem one_add_pow_sub_mem {a : ℕ} {x : AddMonoid.End F} (hx : x ∈ fil F p a) :
    ∀ m : ℕ, (1 + x) ^ m - 1 - (m : AddMonoid.End F) * x -
      (m.choose 2 : AddMonoid.End F) * x ^ 2 ∈ fil F p (a * 3)
  | 0 => by
    rw [show (0 : ℕ).choose 2 = 0 from rfl]
    simp
  | m + 1 => by
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    have e : (1 + x) ^ (m + 1) - 1 - ((m + 1 : ℕ) : AddMonoid.End F) * x -
        ((m + 1).choose 2 : AddMonoid.End F) * x ^ 2 =
        ((1 + x) ^ m - 1 - (m : AddMonoid.End F) * x -
          (m.choose 2 : AddMonoid.End F) * x ^ 2) * (1 + x) +
          (m.choose 2 : AddMonoid.End F) * x ^ 3 := by
      rw [hc, pow_succ]
      push_cast
      noncomm_ring
    rw [e]
    exact add_mem (mul_mem_fil_right _ (one_add_pow_sub_mem hx m))
      (natCast_mul_mem_fil _ (pow_mem_fil hx 3))

theorem one_add_pow_sub_one_mem {a : ℕ} {x : AddMonoid.End F} (hx : x ∈ fil F p a) (m : ℕ) :
    (1 + x) ^ m - 1 ∈ fil F p a := by
  have e : (1 + x) ^ m - 1 = ((1 + x) ^ m - 1 - (m : AddMonoid.End F) * x -
      (m.choose 2 : AddMonoid.End F) * x ^ 2) + (m : AddMonoid.End F) * x +
      (m.choose 2 : AddMonoid.End F) * x ^ 2 := by abel
  rw [e]
  exact add_mem (add_mem (fil_mono (by omega) (one_add_pow_sub_mem hx m))
    (natCast_mul_mem_fil _ hx)) (natCast_mul_mem_fil _ (fil_mono (by omega) (pow_mem_fil hx 2)))

/-- One descent step: if `x ∈ fil F p a` and `(1 + x) ^ ℓ = 1` for a prime `ℓ`, then
`x ∈ fil F p (a + 1)`, provided `1 ≤ a` and `3 ≤ p ∨ 2 ≤ a`. -/
theorem mem_fil_succ [IsAddTorsionFree F] (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a)
    (hpa : 3 ≤ p ∨ 2 ≤ a) {ℓ : ℕ} (hℓ : ℓ.Prime) {x : AddMonoid.End F} (hx : x ∈ fil F p a)
    (h : (1 + x) ^ ℓ = 1) : x ∈ fil F p (a + 1) := by
  have hE := one_add_pow_sub_mem hx ℓ
  have e : (1 + x) ^ ℓ - 1 - (ℓ : AddMonoid.End F) * x - (ℓ.choose 2 : AddMonoid.End F) * x ^ 2 =
      -((ℓ : AddMonoid.End F) * x + (ℓ.choose 2 : AddMonoid.End F) * x ^ 2) := by
    rw [h]
    abel
  rw [e] at hE
  have hE' : (ℓ : AddMonoid.End F) * x + (ℓ.choose 2 : AddMonoid.End F) * x ^ 2 ∈
      fil F p (a * 3) := by
    simpa using neg_mem hE
  have hx2 : x ^ 2 ∈ fil F p (a * 2) := pow_mem_fil hx 2
  by_cases hℓp : ℓ = p
  · rw [hℓp] at hE'
    have hc : (p.choose 2 : AddMonoid.End F) * x ^ 2 ∈ fil F p (a + 1 + 1) := by
      rcases hpa with h3 | h2
      · obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) two_ne_zero (by omega)
        rw [hc, Nat.cast_mul, mul_assoc]
        exact fil_mono (j := a + 1 + 1) (k := a * 2 + 1) (by omega)
          (prime_mul_mem_fil (natCast_mul_mem_fil c hx2))
      · exact fil_mono (j := a + 1 + 1) (k := a * 2) (by omega) (natCast_mul_mem_fil _ hx2)
    have hpx : (p : AddMonoid.End F) * x ∈ fil F p (a + 1 + 1) := by
      have := sub_mem (fil_mono (j := a + 1 + 1) (by omega) hE') hc
      simpa using this
    exact mem_fil_of_prime_mul_mem hp.ne_zero hpx
  · have hℓx : (ℓ : AddMonoid.End F) * x ∈ fil F p (a + 1) := by
      have h2 : (ℓ : AddMonoid.End F) * x ∈ fil F p (a * 2) := by
        simpa using sub_mem (fil_mono (j := a * 2) (by omega) hE')
          (natCast_mul_mem_fil (ℓ.choose 2) hx2)
      exact fil_mono (j := a + 1) (by omega) h2
    have hpx : (p : AddMonoid.End F) ^ (a + 1) * x ∈ fil F p (a + 1) := by
      rw [← Nat.cast_pow]
      intro v
      exact ⟨x v, rfl⟩
    have hcop : IsCoprime (ℓ : ℤ) ((p ^ (a + 1) : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ hp).2 hℓp))
    obtain ⟨u, w, huw⟩ := hcop
    have e : x = (u : AddMonoid.End F) * ((ℓ : AddMonoid.End F) * x) +
        (w : AddMonoid.End F) * ((p : AddMonoid.End F) ^ (a + 1) * x) := by
      have h1 : ((u * ℓ + w * ((p ^ (a + 1) : ℕ) : ℤ) : ℤ) : AddMonoid.End F) = 1 := by
        rw [huw, Int.cast_one]
      push_cast at h1
      rw [← mul_assoc, ← mul_assoc, ← add_mul, h1, one_mul]
    rw [e]
    exact add_mem (mul_mem_fil_left _ hℓx) (mul_mem_fil_left _ hpx)

/-- **Core lemma.** Let `F` be a finitely generated torsion-free abelian group, `p` a prime and
`1 ≤ a` with `3 ≤ p ∨ 2 ≤ a`. An endomorphism `g` of `F` with `g ^ m = 1` for some `m > 0` and
`g - 1` mapping `F` into `p ^ a F` is the identity. -/
theorem eq_one_of_sub_one_mem_fil [IsAddTorsionFree F] [Module.Finite ℤ F] (hp : p.Prime)
    {a : ℕ} (ha : 1 ≤ a) (hpa : 3 ≤ p ∨ 2 ≤ a) {g : AddMonoid.End F} (hg : g - 1 ∈ fil F p a)
    {m : ℕ} (hm : 0 < m) (hgm : g ^ m = 1) : g = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using hgm
    have hℓ : m.minFac.Prime := Nat.minFac_prime hm1
    set m' := m / m.minFac
    have hmm' : m = m' * m.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd m)).symm
    have hm'pos : 0 < m' := Nat.div_pos (Nat.minFac_le hm) hℓ.pos
    have hm'lt : m' < m := Nat.div_lt_self hm hℓ.one_lt
    have hx : g ^ m' - 1 ∈ fil F p a := by
      have := one_add_pow_sub_one_mem hg m'
      rwa [add_sub_cancel] at this
    have hxℓ : (1 + (g ^ m' - 1)) ^ m.minFac = 1 := by
      rw [add_sub_cancel, ← pow_mul, ← hmm', hgm]
    have hall : ∀ k, g ^ m' - 1 ∈ fil F p (a + k) := by
      intro k
      induction k with
      | zero => exact hx
      | succ k ihk =>
        have := mem_fil_succ hp (a := a + k) (by omega) (by omega) hℓ ihk hxℓ
        rwa [← add_assoc]
    have hx0 : g ^ m' - 1 = 0 :=
      eq_zero_of_forall_mem_fil hp fun k => fil_mono (by omega) (hall k)
    exact ih m' hm'lt hm'pos (sub_eq_zero.1 hx0)

end Filtration

/-- Every `n ≥ 3` is divisible by `p ^ a` for a prime `p` and `1 ≤ a` with `3 ≤ p ∨ 2 ≤ a`:
take an odd prime divisor, or `4` if there is none. -/
theorem exists_prime_pow_dvd {n : ℕ} (hn : 3 ≤ n) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ (3 ≤ p ∨ 2 ≤ a) ∧ p ^ a ∣ n := by
  by_cases h4 : 4 ∣ n
  · exact ⟨2, 2, Nat.prime_two, by norm_num, Or.inr le_rfl, by simpa using h4⟩
  · obtain ⟨m, hm2, hmn, hm⟩ : ∃ m, ¬ 2 ∣ m ∧ m ∣ n ∧ 2 ≤ m := by
      by_cases h2 : 2 ∣ n
      · obtain ⟨m, rfl⟩ := h2
        refine ⟨m, ?_, dvd_mul_left _ _, by omega⟩
        rintro ⟨k, rfl⟩
        exact h4 ⟨k, by ring⟩
      · exact ⟨n, h2, dvd_rfl, by omega⟩
    have hp := Nat.minFac_prime (by omega : m ≠ 1)
    refine ⟨m.minFac, 1, hp, le_rfl, Or.inl ?_, by simpa using (Nat.minFac_dvd m).trans hmn⟩
    have h2 := hp.two_le
    have : m.minFac ≠ 2 := fun h => hm2 (h ▸ Nat.minFac_dvd m)
    omega

/-- **Finite-order detection modulo `n`.** -/
theorem finiteOrderCongruenceDetection : FiniteOrderCongruenceDetectionStatement.{u} := by
  intro M _ _ n hn htors σ ⟨r, hr, hσr⟩ hcong
  obtain ⟨p, a, hp, ha, hpa, hdvd⟩ := exists_prime_pow_dvd hn
  have hn0 : n ≠ 0 := by omega
  -- the subgroup `n M`
  let N : AddSubgroup M := AddMonoidHom.range (n : AddMonoid.End M)
  have hmemN : ∀ y : M, n • y ∈ N := fun y => ⟨y, rfl⟩
  have hNmem : ∀ v ∈ N, ∃ y : M, v = n • y := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  -- `n M` is torsion-free
  have htfN : IsAddTorsionFree N := by
    refine ⟨fun k hk v₁ v₂ h => ?_⟩
    have h' : k • ((v₁ : M) - v₂) = 0 := by
      have := congrArg Subtype.val h
      simp only [AddSubgroup.coe_nsmul] at this
      rw [smul_sub, this, sub_self]
    obtain ⟨y, hy⟩ := hNmem _ (N.sub_mem v₁.2 v₂.2)
    have hny : n • y = 0 := htors y ⟨k * n, Nat.mul_pos (Nat.pos_of_ne_zero hk)
      (Nat.pos_of_ne_zero hn0), by rw [mul_smul, ← hy, h']⟩
    exact Subtype.ext (sub_eq_zero.1 (hy.trans hny))
  have hfgN : Module.Finite ℤ N := Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_range _)
  -- the restriction of `σ` to `n M`
  have hσN : ∀ v ∈ N, σ v ∈ N := by
    intro v hv
    obtain ⟨y, rfl⟩ := hNmem v hv
    rw [map_nsmul]
    exact hmemN _
  let g : AddMonoid.End N :=
    AddMonoidHom.mk' (fun v => ⟨σ v, hσN v v.2⟩) (fun v w => Subtype.ext (map_add σ (v : M) (w : M)))
  have hgpow : ∀ (k : ℕ) (v : N),
      (((g ^ k) v : N) : M) = ((σ.toEquiv : Equiv.Perm M) ^ k) (v : M) := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, pow_zero]; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply]
      exact ih (g v)
  have hgr : g ^ r = 1 := by
    ext v
    rw [hgpow, hσr]
    rfl
  have hgfil : g - 1 ∈ fil N p a := by
    obtain ⟨c, hc⟩ := hdvd
    rintro ⟨v, hv⟩
    obtain ⟨y, rfl⟩ := hNmem v hv
    obtain ⟨z, hz⟩ := hcong y
    refine ⟨⟨c • (n • z), N.nsmul_mem (hmemN z) c⟩, Subtype.ext ?_⟩
    change σ (n • y) - n • y = (p ^ a) • (c • (n • z))
    rw [map_nsmul, hz, smul_add, add_sub_cancel_left, ← mul_smul (p ^ a) c, ← hc]
  have hg1 : g = 1 := eq_one_of_sub_one_mem_fil hp ha hpa hgfil hr hgr
  ext x
  obtain ⟨y, hy⟩ := hcong x
  have h1 : σ (n • x) = n • x := by
    have := congrArg (fun f : AddMonoid.End N => ((f ⟨n • x, hmemN x⟩ : N) : M)) hg1
    exact this
  have h2 : n • (n • y) = 0 := by
    rw [← (sub_eq_iff_eq_add').2 hy, smul_sub, ← map_nsmul, h1, sub_self]
  have h3 : n • y = 0 := htors y ⟨n * n, Nat.mul_pos (Nat.pos_of_ne_zero hn0)
    (Nat.pos_of_ne_zero hn0), by rw [mul_smul]; exact h2⟩
  rw [hy, h3, add_zero]
  rfl

end Langlands.FiniteOrderCongruence
