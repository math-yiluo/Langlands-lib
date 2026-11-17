import Langlands.GroupScheme.Torus.TorsionDensityLattice
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.CharP.Basic

/-! # Group-algebra facts behind torsion determination -/

universe u

open AddMonoidAlgebra

namespace Langlands.GroupScheme.TorsionDetermination

/-- In a finitely generated abelian group, a nonzero element is not divisible by some positive
integer. -/
theorem exists_not_mem_nsmulSubgroup {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ] {d : Λ}
    (hd : d ≠ 0) : ∃ n : ℕ, 0 < n ∧ d ∉ TorsionDensity.multiples Λ n := by
  obtain ⟨I, A, _, _, _, ⟨e⟩⟩ := Diagonalizable.exists_freeFiniteEquiv Λ
  by_cases h1 : (e d).1 = 0
  · have h2 : (e d).2 ≠ 0 := by
      intro h2
      exact hd (e.injective (by rw [map_zero]; exact Prod.ext h1 h2))
    refine ⟨Nat.card A, Nat.card_pos, ?_⟩
    rintro ⟨x, rfl⟩
    apply h2
    simp
  · obtain ⟨i, hi⟩ : ∃ i, (e d).1 i ≠ 0 := by
      by_contra h
      push Not at h
      exact h1 (funext h)
    set n : ℕ := ((e d).1 i).natAbs + 1 with hn
    refine ⟨n, by omega, ?_⟩
    rintro ⟨x, hx⟩
    have hxi : (n : ℤ) * (e x).1 i = (e d).1 i := by
      rw [← hx, nsmulAddMonoidHom_apply, map_nsmul, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul]
    have habs := congrArg Int.natAbs hxi
    rw [Int.natAbs_mul, Int.natAbs_natCast] at habs
    have hne : ((e x).1 i).natAbs ≠ 0 := by
      intro h0
      rw [Int.natAbs_eq_zero.mp h0, mul_zero] at hxi
      exact hi hxi.symm
    have : n * 1 ≤ n * ((e x).1 i).natAbs :=
      Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hne)
    omega

/-- For finitely many elements of a finitely generated abelian group, reduction modulo `nΛ`
is injective on them for some positive `n`. -/
theorem exists_injOn_mk_nsmulSubgroup {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    (s : Finset Λ) :
    ∃ n : ℕ, 0 < n ∧
      Set.InjOn (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n)) (s : Set Λ) := by
  classical
  have hex : ∀ p : Λ × Λ, ∃ n : ℕ, 0 < n ∧ (p.1 ≠ p.2 → -p.1 + p.2 ∉ TorsionDensity.multiples Λ n) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => (h hp).elim⟩
    · obtain ⟨n, hn, hn'⟩ := exists_not_mem_nsmulSubgroup (Λ := Λ) (d := -p.1 + p.2) (by
        intro h
        apply hp
        rw [neg_add_eq_zero] at h
        exact h)
      exact ⟨n, hn, fun _ => hn'⟩
  choose m hm0 hm using hex
  refine ⟨∏ p ∈ s ×ˢ s, m p, Finset.prod_pos fun p _ => hm0 p, ?_⟩
  intro a ha b hb hab
  by_contra hne
  have hmem : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
  apply hm (a, b) hne
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hab
  obtain ⟨x, hx⟩ := hab
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hmem
  refine ⟨k • x, ?_⟩
  change m (a, b) • k • x = -a + b
  rw [smul_smul, ← hk]
  exact hx

theorem coeff_mapDomain_of_injOn {R M N : Type*} [Semiring R] {f : M → N} (x : R[M])
    (hf : Set.InjOn f (x.coeff.support : Set M)) {a : M} (ha : a ∈ x.coeff.support) :
    (mapDomain f x).coeff (f a) = x.coeff a := by
  rw [coeff_mapDomain]
  exact Finsupp.mapDomain_apply' _ x.coeff le_rfl hf ha

theorem mapDomain_ne_zero_of_injOn {R M N : Type*} [Semiring R] {f : M → N} {x : R[M]}
    (hx : x ≠ 0) (hf : Set.InjOn f (x.coeff.support : Set M)) : mapDomain f x ≠ 0 := by
  obtain ⟨a, ha⟩ : x.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hx (AddMonoidAlgebra.coeff_injective (by rw [h]; rfl))
  intro h0
  have := coeff_mapDomain_of_injOn x hf ha
  rw [h0] at this
  exact (Finsupp.mem_support_iff.mp ha) this.symm

/-- **Torsion quotients detect group-algebra elements.** A nonzero element of `R[Λ]`, for a
finitely generated abelian group `Λ`, has nonzero image in `R[Λ/nΛ]` for some `n > 0`. -/
theorem exists_mapDomain_mk_ne_zero {R : Type*} [Semiring R] {Λ : Type u} [AddCommGroup Λ]
    [AddGroup.FG Λ] {x : R[Λ]} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ mapDomain (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n)) x ≠ 0 := by
  obtain ⟨n, hn, hinj⟩ := exists_injOn_mk_nsmulSubgroup (Λ := Λ) x.coeff.support
  exact ⟨n, hn, mapDomain_ne_zero_of_injOn hx hinj⟩

/-- Reduction `ℤ^I → (ℤ/n)^I`. -/
abbrev castPi (I : Type*) (n : ℕ) : (I → ℤ) →+ (I → ZMod n) :=
  (Int.castAddHom (ZMod n)).compLeft I

/-- Over a field `K`, the group algebra `K[(ℤ/n)^I]` is reduced when `n` is invertible in `K`
(Maschke). -/
theorem isReduced_zmod {K : Type*} [Field K] (I : Type*) [Finite I] (n : ℕ) [NeZero n]
    (hn : (n : K) ≠ 0) : IsReduced (AddMonoidAlgebra K (I → ZMod n)) := by
  have : NeZero (Nat.card (I → ZMod n) : K) := by
    refine ⟨?_⟩
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact pow_ne_zero _ hn
  infer_instance

/-- **Separable torsion quotients detect Laurent polynomials.** Over a field `K`, a nonzero element
of `K[ℤ^I]` (with `I` finite) has non-nilpotent image in `K[(ℤ/n)^I]` for some `n > 0` with `n`
invertible in `K`. -/
theorem exists_not_isNilpotent_mapDomain_castPi {K : Type*} [Field K] {I : Type*} [Fintype I]
    {x : K[I → ℤ]} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : K) ≠ 0 ∧ ¬ IsNilpotent (mapDomain (castPi I n) x) := by
  classical
  set s := x.coeff.support
  set B : ℕ := ∑ μ ∈ s, ∑ i, (μ i).natAbs
  have hB : ∀ μ ∈ s, ∀ i, (μ i).natAbs ≤ B := by
    intro μ hμ i
    refine le_trans ?_ (Finset.single_le_sum (f := fun μ : I → ℤ => ∑ i, (μ i).natAbs)
      (fun _ _ => Nat.zero_le _) hμ)
    exact Finset.single_le_sum (f := fun i => (μ i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (2 * B + ringChar K + 2)
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [ringChar.spec] at h
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · rcases (Nat.prime_def.mp hp).2 _ h with h1 | h1
      · exact hq.one_lt.ne' h1
      · omega
    · rw [hq, zero_dvd_iff] at h
      exact hp.ne_zero h
  have : NeZero p := ⟨hp.ne_zero⟩
  have hinj : Set.InjOn (castPi I p) (s : Set (I → ℤ)) := by
    intro μ hμ ν hν h
    funext i
    have hi := congrFun h i
    simp only [castPi, AddMonoidHom.compLeft_apply, Function.comp_apply, Int.coe_castAddHom] at hi
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    have hlt : |ν i - μ i| < (p : ℤ) := by
      have h1 := hB μ hμ i
      have h2 := hB ν hν i
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hi hlt
    omega
  refine ⟨p, hp.pos, hpK, ?_⟩
  have := isReduced_zmod (K := K) I p hpK
  rw [isNilpotent_iff_eq_zero]
  exact mapDomain_ne_zero_of_injOn hx hinj

end Langlands.GroupScheme.TorsionDetermination
