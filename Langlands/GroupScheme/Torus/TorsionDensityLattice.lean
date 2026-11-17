import Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Separating group-ring elements by the quotients `Λ ⧸ nΛ` -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.TorsionDensity

/-- The subgroup `nΛ` of `n`-fold multiples in an abelian group `Λ`. -/
abbrev multiples (Λ : Type u) [AddCommGroup Λ] (n : ℕ) : AddSubgroup Λ :=
  (nsmulAddMonoidHom n : Λ →+ Λ).range

theorem mem_multiples {Λ : Type u} [AddCommGroup Λ] {n : ℕ} {d : Λ} :
    d ∈ multiples Λ n ↔ ∃ x : Λ, n • x = d := by
  simp [multiples]

theorem nsmul_mem_multiples {Λ : Type u} [AddCommGroup Λ] (n : ℕ) (x : Λ) :
    n • x ∈ multiples Λ n :=
  mem_multiples.mpr ⟨x, rfl⟩

section Bound

variable {Λ : Type u} [AddCommGroup Λ] {I A : Type v} [Fintype I] [AddCommGroup A]
  (b : Λ ≃+ (I → ℤ) × A)

include b in
/-- A nonzero element of `Λ ≃ ℤ^I × A` (`A` finite) is not a multiple of `n` once `n` is a
multiple of `|A|` exceeding the sum of the absolute values of its free coordinates. -/
theorem exists_bound_of_ne_zero {d : Λ} (hd : d ≠ 0) :
    ∃ M : ℕ, ∀ n : ℕ, Nat.card A ∣ n → M < n → d ∉ multiples Λ n := by
  classical
  refine ⟨∑ i, ((b d).1 i).natAbs, fun n hN hM hmem => hd ?_⟩
  obtain ⟨x, hx⟩ := mem_multiples.mp hmem
  have hA : n • (b x).2 = 0 := by
    obtain ⟨c, rfl⟩ := hN
    rw [mul_comm, mul_nsmul, card_nsmul_eq_zero']
  have h1 : (b d).1 = n • (b x).1 := by
    rw [← hx, map_nsmul, Prod.smul_fst]
  have h2 : (b d).2 = 0 := by
    rw [← hx, map_nsmul, Prod.smul_snd, hA]
  have hc : ∀ i, (b x).1 i = 0 := by
    intro i
    by_contra hci
    have hle : ((b d).1 i).natAbs ≤ ∑ j, ((b d).1 j).natAbs :=
      Finset.single_le_sum (f := fun j => ((b d).1 j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have heq : ((b d).1 i).natAbs = n * ((b x).1 i).natAbs := by
      rw [h1, Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have hpos : 1 ≤ ((b x).1 i).natAbs := Int.natAbs_pos.mpr hci
    have : n ≤ n * ((b x).1 i).natAbs := Nat.le_mul_of_pos_right n hpos
    omega
  apply b.injective
  rw [map_zero]
  refine Prod.ext ?_ h2
  rw [h1]
  funext i
  simp [hc i]

include b in
/-- For a finite subset `s` of `Λ`, the quotient map `Λ → Λ ⧸ nΛ` is injective on `s` once `n` is
a large enough multiple of `|A|`. -/
theorem exists_bound_injOn (s : Finset Λ) :
    ∃ M : ℕ, ∀ n : ℕ, Nat.card A ∣ n → M < n →
      Set.InjOn (QuotientAddGroup.mk' (multiples Λ n)) (s : Set Λ) := by
  classical
  have hex : ∀ d : Λ, ∃ M : ℕ, d ≠ 0 → ∀ n : ℕ, Nat.card A ∣ n → M < n →
      d ∉ multiples Λ n := by
    intro d
    by_cases hd : d = 0
    · exact ⟨0, fun h => (h hd).elim⟩
    · obtain ⟨M, hM⟩ := exists_bound_of_ne_zero b hd
      exact ⟨M, fun _ => hM⟩
  choose M hM using hex
  refine ⟨(s ×ˢ s).sup (fun p => M (p.1 - p.2)), fun n hN hn a ha c hc hac => ?_⟩
  by_contra hne
  have hle : M (a - c) ≤ (s ×ˢ s).sup (fun p => M (p.1 - p.2)) :=
    Finset.le_sup (f := fun p : Λ × Λ => M (p.1 - p.2)) (b := (a, c))
      (Finset.mem_product.mpr ⟨Finset.mem_coe.mp ha, Finset.mem_coe.mp hc⟩)
  apply hM (a - c) (sub_ne_zero.mpr hne) n hN (lt_of_le_of_lt hle hn)
  exact (QuotientAddGroup.eq_iff_sub_mem).mp hac

end Bound

/-- An element of a monoid algebra is zero if its image under a map of the exponent set which is
injective on its support vanishes. -/
theorem eq_zero_of_mapDomain_eq_zero {R : Type*} [Semiring R] {α β : Type*} (q : α → β)
    (f : AddMonoidAlgebra R α) (hq : Set.InjOn q (f.coeff.support : Set α))
    (h : AddMonoidAlgebra.mapDomain q f = 0) : f = 0 := by
  have h' : Finsupp.mapDomain q f.coeff = 0 := by
    have := congrArg AddMonoidAlgebra.coeff h
    simpa using this
  have hc : f.coeff = 0 := by
    ext a
    by_contra ha
    have := Finsupp.mapDomain_apply' (f.coeff.support : Set α) f.coeff subset_rfl hq
      (Finsupp.mem_support_iff.mpr ha)
    rw [h'] at this
    exact ha (by simpa using this.symm)
  rw [← AddMonoidAlgebra.ofCoeff_coeff f, hc, AddMonoidAlgebra.ofCoeff_zero]

/-- **Separation by the quotients `Λ ⧸ nΛ`.** For a finitely generated abelian group `Λ` there is
`N > 0`, all of whose prime divisors are orders of elements of `Λ`, such that every nonzero
element of a monoid algebra `R[Λ]` stays nonzero in `R[Λ ⧸ nΛ]` for every large enough multiple
`n` of `N`. -/
theorem exists_separating (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    ∃ N : ℕ, 0 < N ∧ (∀ p : ℕ, p.Prime → p ∣ N → ∃ x : Λ, x ≠ 0 ∧ p • x = 0) ∧
      ∀ (R : Type v) [Semiring R] (f : AddMonoidAlgebra R Λ), f ≠ 0 →
        ∃ M : ℕ, ∀ n : ℕ, N ∣ n → M < n →
          AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' (multiples Λ n)) f ≠ 0 := by
  classical
  obtain ⟨I, A, hI, hA, hfin, ⟨b⟩⟩ := Diagonalizable.exists_freeFiniteEquiv Λ
  refine ⟨Nat.card A, Nat.card_pos, ?_, ?_⟩
  · intro p hp hpN
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' p hpN
    refine ⟨b.symm (0, a), ?_, ?_⟩
    · intro h0
      have h := congrArg b h0
      rw [AddEquiv.apply_symm_apply, map_zero, Prod.mk_eq_zero] at h
      have : addOrderOf a = 1 := by rw [h.2, addOrderOf_zero]
      exact hp.one_lt.ne' (ha ▸ this)
    · rw [← map_nsmul, Prod.smul_mk, smul_zero, ← ha, addOrderOf_nsmul_eq_zero,
        Prod.mk_zero_zero, map_zero]
  · intro R _ f hf
    obtain ⟨M, hM⟩ := exists_bound_injOn b f.coeff.support
    exact ⟨M, fun n hN hn h => hf (eq_zero_of_mapDomain_eq_zero _ f (hM n hN hn) h)⟩

end Langlands.GroupScheme.TorsionDensity
