import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

open scoped BigOperators

namespace Langlands.Algebra.Rosenlicht

open MvPolynomial

universe u v w

variable {k : Type u} [Field k] {σ : Type v} [Fintype σ]

/-- Degree-reducing relations for the coordinate powers give a finite algebra. -/
theorem finite_of_degree_reductions {R : Type w} [CommRing R] [Algebra k R]
    (f : MvPolynomial σ k →ₐ[k] R) (hf : Function.Surjective f)
    (n : σ → ℕ) (q : σ → MvPolynomial σ k)
    (hq : ∀ i, (q i).totalDegree < n i)
    (hrel : ∀ i, f (X i ^ n i) = f (q i)) : Module.Finite k R := by
  classical
  let D : ℕ := ∑ i, n i
  let S : Set R := (fun d : σ →₀ ℕ => f (monomial d 1)) '' {d | d.degree ≤ D}
  let U : Submodule k R := Submodule.span k S
  have hS : S.Finite := (Finsupp.finite_of_degree_le D).image _
  have hmon : ∀ m, ∀ d : σ →₀ ℕ, d.degree = m → ∀ c : k, f (monomial d c) ∈ U := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro d hd c
      by_cases hsmall : d.degree ≤ D
      · have hmem : f (monomial d 1) ∈ U :=
          Submodule.subset_span ⟨d, hsmall, rfl⟩
        simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using U.smul_mem c hmem
      · have hex : ∃ i, n i ≤ d i := by
          by_contra h
          push Not at h
          have hb : d.degree ≤ D := by
            rw [Finsupp.degree_eq_sum]
            exact Finset.sum_le_sum fun i _ => (h i).le
          exact hsmall hb
        obtain ⟨i, hi⟩ := hex
        let e : σ →₀ ℕ := d - Finsupp.single i (n i)
        have he : e + Finsupp.single i (n i) = d :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
        have hdeg : e.degree + n i = m := by
          have := congrArg Finsupp.degree he
          simpa only [map_add, Finsupp.degree_single, hd] using this
        have hreduce : f (monomial d c) = f (monomial e c * q i) := by
          calc
            f (monomial d c) = f (monomial e c * X i ^ n i) := by
              rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, he]
            _ = f (monomial e c * q i) := by rw [map_mul, hrel, ← map_mul]
        rw [hreduce, (q i).as_sum, Finset.mul_sum, map_sum]
        apply U.sum_mem
        intro t ht
        rw [monomial_mul_monomial]
        apply ih (e.degree + t.degree)
        · have htdeg : t.degree ≤ (q i).totalDegree := le_totalDegree ht
          have := hq i
          omega
        · exact map_add Finsupp.degree e t
  have htop : U = ⊤ := by
    apply top_unique
    intro r _
    obtain ⟨p, rfl⟩ := hf r
    rw [p.as_sum, map_sum]
    exact U.sum_mem fun d _ => hmon d.degree d rfl _
  have hfg : U.FG := Submodule.fg_span hS
  exact ⟨htop ▸ hfg⟩

attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] in
/-- Extract the component of a product by a linear homogeneous polynomial. -/
theorem homogeneousComponent_linear_mul (L p : MvPolynomial σ k)
    (hL : L.IsHomogeneous 1) (n : ℕ) (hn : 1 ≤ n) :
    homogeneousComponent n (L * p) = L * homogeneousComponent (n - 1) p := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_le
    (homogeneousSubmodule σ k) (b := p) hL hn
  change (MvPolynomial.decomposition.decompose' (L * p) n : MvPolynomial σ k) =
    L * (MvPolynomial.decomposition.decompose' p (n - 1) : MvPolynomial σ k) at h
  simpa only [MvPolynomial.decomposition.decompose'_apply] using h

/-- A homogeneous cone meeting the hyperplane `L = 0` only at its vertex has
a finite coordinate algebra in the chart `L = 1`. -/
theorem finite_of_homogeneous_chart [IsAlgClosed k]
    {R : Type w} [CommRing R] [Algebra k R]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (L : MvPolynomial σ k) (hL : L.IsHomogeneous 1)
    (hzero : ∀ x : σ → k, (∀ p ∈ I, aeval x p = 0) → aeval x L = 0 → x = 0)
    (f : MvPolynomial σ k →ₐ[k] R) (hf : Function.Surjective f)
    (hfI : ∀ p ∈ I, f p = 0) (hfL : f L = 1) : Module.Finite k R := by
  classical
  let J : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {L}
  have hpow : ∀ i : σ, ∃ n : ℕ, 0 < n ∧ X i ^ n ∈ J := by
    intro i
    have hx : X i ∈ J.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (k := k) (K := k) J]
      intro x hx
      have hxI : ∀ p ∈ I, aeval x p = 0 :=
        fun p hp => hx p (Submodule.mem_sup_left hp)
      have hxL : aeval x L = 0 :=
        hx L (Submodule.mem_sup_right (Ideal.subset_span (by simp)))
      have hx0 := hzero x hxI hxL
      simp [hx0]
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    refine ⟨n + 1, Nat.succ_pos _, ?_⟩
    simpa [pow_succ, mul_comm] using J.mul_mem_left (X i) hn
  have hred : ∀ i : σ, ∃ n : ℕ, ∃ q : MvPolynomial σ k,
      q.totalDegree < n ∧ f (X i ^ n) = f q := by
    intro i
    obtain ⟨n, hn, hp⟩ := hpow i
    obtain ⟨p, hpI, t, ht, hpt⟩ := Submodule.mem_sup.mp hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ht
    let q : MvPolynomial σ k := homogeneousComponent (n - 1) r
    refine ⟨n, q, ?_, ?_⟩
    · dsimp only [q]
      exact lt_of_le_of_lt (homogeneousComponent_isHomogeneous (n - 1) r).totalDegree_le
        (by omega)
    · have hh := congrArg (homogeneousComponent n) hpt
      rw [map_add, homogeneousComponent_linear_mul L r hL n (by omega),
        homogeneousComponent_eq_self (isHomogeneous_X_pow i n)] at hh
      have hmap := congrArg f hh
      rw [map_add, map_mul, hfI _ (homogeneousComponent_mem_of_mem hI hpI n),
        hfL, zero_add, one_mul] at hmap
      exact hmap.symm
  choose n q hq hrel using hred
  exact finite_of_degree_reductions f hf n q hq hrel

/-- The rational points of such a chart form a finite set. -/
theorem finite_points_of_homogeneous_chart [IsAlgClosed k]
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    (L : MvPolynomial σ k) (hL : L.IsHomogeneous 1)
    (hzero : ∀ x : σ → k, (∀ p ∈ I, aeval x p = 0) → aeval x L = 0 → x = 0) :
    Set.Finite {x : σ → k | (∀ p ∈ I, aeval x p = 0) ∧ aeval x L = 1} := by
  classical
  let J : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {L - 1}
  let f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⧸ J := Ideal.Quotient.mkₐ k J
  have hfI : ∀ p ∈ I, f p = 0 := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_left hp)
  have hfL : f L = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one f, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Submodule.mem_sup_right (Ideal.subset_span (by simp)))
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    finite_of_homogeneous_chart I hI L hL hzero f (Ideal.Quotient.mkₐ_surjective k J) hfI hfL
  let S : Set (σ → k) := {x | (∀ p ∈ I, aeval x p = 0) ∧ aeval x L = 1}
  have hkill (x : S) : J ≤ RingHom.ker (aeval x.1 : MvPolynomial σ k →ₐ[k] k) := by
    apply sup_le
    · intro p hp
      exact x.2.1 p hp
    · apply Ideal.span_le.mpr
      intro p hp
      have hp' : p = L - 1 := Set.mem_singleton_iff.mp hp
      subst p
      change aeval x.1 (L - 1) = 0
      rw [map_sub, x.2.2, map_one, sub_self]
  let g : S → (MvPolynomial σ k ⧸ J →ₐ[k] k) :=
    fun x => Ideal.Quotient.liftₐ J (aeval x.1) (hkill x)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    funext i
    have he := congrArg (fun a : MvPolynomial σ k ⧸ J →ₐ[k] k => a (f (X i))) h
    change aeval x.1 (X i) = aeval y.1 (X i) at he
    simpa only [aeval_X] using he
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

end Langlands.Algebra.Rosenlicht
