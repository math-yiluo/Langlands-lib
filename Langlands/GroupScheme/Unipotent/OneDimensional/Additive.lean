import Langlands.GroupScheme.Unipotent.OneDimensional.Cocycle
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Additive polynomials and the Euclidean algorithm for them -/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.Unipotent.OneDimensional

variable {k : Type*} [Field k]

/-- A polynomial `f` is additive when `f(X + Y) = f(X) + f(Y)`. -/
def IsAdditive (f : k[X]) : Prop :=
  coboundary f = 0

theorem IsAdditive.aeval_add {f : k[X]} (hf : IsAdditive f) {R : Type*} [CommRing R]
    [Algebra k R] (u v : R) : aeval (u + v) f = aeval u f + aeval v f := by
  have h := ev2_coboundary u v f
  rw [show coboundary f = 0 from hf, map_zero] at h
  linear_combination -h

theorem isAdditive_of_aeval (f : k[X])
    (h : aeval (C X + X : k[X][X]) f = aeval (C X : k[X][X]) f + aeval (X : k[X][X]) f) :
    IsAdditive f := by
  show coboundary f = 0
  rw [coboundary, h]
  ring

theorem isAdditive_zero : IsAdditive (0 : k[X]) :=
  coboundary_zero

theorem isAdditive_X : IsAdditive (X : k[X]) :=
  isAdditive_of_aeval _ (by simp)

theorem IsAdditive.add {f g : k[X]} (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (f + g) :=
  isAdditive_of_aeval _ (by simp only [map_add, hf.aeval_add, hg.aeval_add]; ring)

theorem IsAdditive.neg {f : k[X]} (hf : IsAdditive f) : IsAdditive (-f) :=
  isAdditive_of_aeval _ (by simp only [map_neg, hf.aeval_add]; ring)

theorem IsAdditive.sub {f g : k[X]} (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem IsAdditive.C_mul {f : k[X]} (hf : IsAdditive f) (a : k) : IsAdditive (C a * f) :=
  isAdditive_of_aeval _ (by simp only [map_mul, aeval_C, hf.aeval_add]; ring)

theorem IsAdditive.comp {f g : k[X]} (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (f.comp g) :=
  isAdditive_of_aeval _ (by rw [aeval_comp, aeval_comp, aeval_comp, hg.aeval_add, hf.aeval_add])

theorem isAdditive_X_pow (q : ℕ) [ExpChar k q] (n : ℕ) : IsAdditive (X ^ q ^ n : k[X]) :=
  isAdditive_of_aeval _ (by
    simp only [map_pow, aeval_X]
    exact add_pow_expChar_pow (C X : k[X][X]) (X : k[X][X]) (p := q) (n := n))

theorem IsAdditive.coeff_zero {f : k[X]} (hf : IsAdditive f) : f.coeff 0 = 0 := by
  have h := coeff_zero_coboundary f
  rw [show coboundary f = 0 from hf, Polynomial.coeff_zero, eq_comm, neg_eq_zero, C_eq_zero] at h
  exact h

theorem IsAdditive.aeval_zero {f : k[X]} (hf : IsAdditive f) {R : Type*} [CommRing R]
    [Algebra k R] : aeval (0 : R) f = 0 := by
  rw [aeval_def, eval₂_at_zero, hf.coeff_zero, map_zero]

/-- The binomial coefficients of the degree of an additive polynomial vanish in `k`. -/
theorem IsAdditive.choose_eq_zero {f : k[X]} (hf : IsAdditive f) {j : ℕ} (hj0 : 0 < j)
    (hjn : j < f.natDegree) : ((f.natDegree.choose j : ℕ) : k) = 0 := by
  have h := congrArg (fun c : k[X][X] => (c.coeff j).coeff (f.natDegree - j))
    (show coboundary f = 0 from hf)
  simp only [coeff_coboundary, coeff_sub, hasseDeriv_coeff, coeff_C, Polynomial.coeff_zero] at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.sub_add_cancel hjn.le] at h
  simp only [Polynomial.coeff_zero, sub_zero] at h
  have hlc : f.coeff f.natDegree ≠ 0 := by
    rw [coeff_natDegree, Ne, leadingCoeff_eq_zero]
    rintro rfl
    simp at hjn
  exact (mul_eq_zero.mp h).resolve_right hlc

/-- If a prime `p` divides all inner binomial coefficients of `n ≥ 1`, then `n` is a power
of `p`. -/
theorem eq_pow_of_dvd_choose {p : ℕ} [hp : Fact p.Prime] :
    ∀ n : ℕ, 0 < n → (∀ j, 0 < j → j < n → p ∣ n.choose j) → ∃ a, n = p ^ a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hdvd
  have hp2 := hp.out.two_le
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    obtain ⟨a, rfl⟩ := ih m (by nlinarith) hm fun j hj0 hjm => by
      have h1 := hdvd (p * j) (by positivity) (Nat.mul_lt_mul_of_pos_left hjm (by omega))
      have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * m) (k := p * j)
        (p := p)
      rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.choose_self, one_mul,
        Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)] at hL
      exact (Nat.modEq_zero_iff_dvd.mp (hL.symm.trans (Nat.modEq_zero_iff_dvd.mpr h1)))
    exact ⟨a + 1, by rw [pow_succ, mul_comm]⟩
  · rcases Nat.lt_or_ge n 2 with h | h
    · exact ⟨0, by rw [pow_zero]; omega⟩
    · exact absurd (by simpa using hdvd 1 one_pos (by omega)) hpn

/-- A nonzero additive polynomial has degree a power of the characteristic exponent. -/
theorem IsAdditive.natDegree_eq_pow (q : ℕ) [hq : ExpChar k q] {f : k[X]} (hf : IsAdditive f)
    (h0 : f ≠ 0) : ∃ a, f.natDegree = q ^ a := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    intro hd
    apply h0
    rw [eq_C_of_natDegree_eq_zero hd, hf.coeff_zero, C_0]
  cases hq with
  | zero =>
    refine ⟨0, ?_⟩
    by_contra hne
    have h := hf.choose_eq_zero one_pos (by rw [pow_zero] at hne; omega)
    rw [Nat.choose_one_right, Nat.cast_eq_zero] at h
    omega
  | prime hp =>
    have : Fact q.Prime := ⟨hp⟩
    refine eq_pow_of_dvd_choose f.natDegree hpos fun j hj0 hjn => ?_
    exact (CharP.cast_eq_zero_iff k q _).mp (hf.choose_eq_zero hj0 hjn)

/-- Leading-term elimination: an additive polynomial of at least the degree of a nonzero
additive polynomial `β` is reduced in degree by subtracting `β ∘ ρ` for an additive monomial
`ρ`. -/
theorem exists_reduce (q : ℕ) [ExpChar k q] [PerfectRing k q] {α β : k[X]} (hα : IsAdditive α)
    (hβ : IsAdditive β) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hle : β.natDegree ≤ α.natDegree) :
    ∃ ρ : k[X], IsAdditive ρ ∧
      (α - β.comp ρ = 0 ∨ (α - β.comp ρ).natDegree < α.natDegree) := by
  obtain ⟨a, ha⟩ := hα.natDegree_eq_pow q hα0
  obtain ⟨b, hb⟩ := hβ.natDegree_eq_pow q hβ0
  have hq0 : q ≠ 0 := (expChar_pos k q).ne'
  have hpow : q ^ b * q ^ (a - b) = q ^ a := by
    rcases Nat.lt_or_ge 1 q with hq1 | hq1
    · rw [ha, hb] at hle
      rw [← pow_add, Nat.add_sub_cancel' ((Nat.pow_le_pow_iff_right hq1).mp hle)]
    · have hq1' : q = 1 := le_antisymm hq1 (expChar_pos k q)
      subst hq1'
      simp
  set e : k := (iterateFrobeniusEquiv k q b).symm (α.leadingCoeff / β.leadingCoeff) with he
  have hepow : e ^ q ^ b = α.leadingCoeff / β.leadingCoeff := by
    rw [← iterateFrobeniusEquiv_def, he, RingEquiv.apply_symm_apply]
  have hlcβ : β.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hβ0
  have hlcα : α.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hα0
  have he0 : e ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero _ hq0)] at hepow
    exact div_ne_zero hlcα hlcβ hepow.symm
  refine ⟨C e * X ^ q ^ (a - b), (isAdditive_X_pow q _).C_mul e, ?_⟩
  by_cases hzero : α - β.comp (C e * X ^ q ^ (a - b)) = 0
  · exact Or.inl hzero
  right
  have hρdeg : (C e * X ^ q ^ (a - b)).natDegree = q ^ (a - b) := natDegree_C_mul_X_pow _ _ he0
  have hρ0 : (C e * X ^ q ^ (a - b)).natDegree ≠ 0 := by
    rw [hρdeg]
    exact pow_ne_zero _ hq0
  have hdeg : (β.comp (C e * X ^ q ^ (a - b))).natDegree = α.natDegree := by
    rw [natDegree_comp, hρdeg, hb, ha, hpow]
  have hlc : α.leadingCoeff = (β.comp (C e * X ^ q ^ (a - b))).leadingCoeff := by
    rw [leadingCoeff_comp hρ0, leadingCoeff_C_mul_X_pow, hb, hepow, mul_div_cancel₀ _ hlcβ]
  have hcomp0 : β.comp (C e * X ^ q ^ (a - b)) ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hlc
    exact hlcα hlc
  have hd : α.degree = (β.comp (C e * X ^ q ^ (a - b))).degree := by
    rw [degree_eq_natDegree hα0, degree_eq_natDegree hcomp0, hdeg]
  have hlt := degree_sub_lt_left hd hα0 hlc
  rw [degree_eq_natDegree hzero, degree_eq_natDegree hα0, Nat.cast_lt] at hlt
  exact hlt

section Euclid

variable {B : Type*} [CommRing B] [Algebra k B]

/-- **Euclid's algorithm for additive polynomials.** Let `P` be a set of elements closed under
additive polynomials and subtraction, on which nonzero polynomials do not vanish except at `0`.
Two elements of `P` satisfying a nontrivial additive relation are both additive polynomials in
a single element of `P`. -/
theorem exists_common_of_relation (q : ℕ) [ExpChar k q] [PerfectRing k q] (P : Set B)
    (hP : ∀ u ∈ P, ∀ A : k[X], IsAdditive A → aeval u A ∈ P)
    (hsub : ∀ u ∈ P, ∀ v ∈ P, u - v ∈ P)
    (htr : ∀ u ∈ P, ∀ A : k[X], A ≠ 0 → aeval u A = 0 → u = 0) :
    ∀ (N : ℕ) (u v : B) (α β : k[X]), α.natDegree + β.natDegree ≤ N → u ∈ P → v ∈ P →
      IsAdditive α → IsAdditive β → α ≠ 0 → β ≠ 0 → aeval u α = aeval v β →
      ∃ s ∈ P, ∃ A A' : k[X], IsAdditive A ∧ IsAdditive A' ∧ u = aeval s A ∧ v = aeval s A' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  -- The reduction step, when `deg β ≤ deg α`.
  have step : ∀ (u v : B) (α β : k[X]), α.natDegree + β.natDegree ≤ N → u ∈ P → v ∈ P →
      IsAdditive α → IsAdditive β → α ≠ 0 → β ≠ 0 → aeval u α = aeval v β →
      β.natDegree ≤ α.natDegree →
      ∃ s ∈ P, ∃ A A' : k[X], IsAdditive A ∧ IsAdditive A' ∧ u = aeval s A ∧
        v = aeval s A' := by
    intro u v α β hN hu hv hα hβ hα0 hβ0 hrel hle
    obtain ⟨ρ, hρ, hred⟩ := exists_reduce q hα hβ hα0 hβ0 hle
    have hv' : v - aeval u ρ ∈ P := hsub v hv _ (hP u hu ρ hρ)
    have hrel' : aeval u (α - β.comp ρ) = aeval (v - aeval u ρ) β := by
      have h := hβ.aeval_add (v - aeval u ρ) (aeval u ρ)
      rw [sub_add_cancel] at h
      rw [map_sub, aeval_comp, hrel, h]
      ring
    by_cases h0 : α - β.comp ρ = 0
    · have hz : v - aeval u ρ = 0 := by
        refine htr _ hv' β hβ0 ?_
        rw [← hrel', h0, map_zero]
      refine ⟨u, hu, X, ρ, isAdditive_X, hρ, by simp, ?_⟩
      exact (sub_eq_zero.mp hz)
    · have hlt := hred.resolve_left h0
      obtain ⟨s, hs, A, A'', hA, hA'', hus, hvs⟩ :=
        ih _ (by omega) u (v - aeval u ρ) (α - β.comp ρ) β le_rfl hu hv'
          (hα.sub (hβ.comp hρ)) hβ h0 hβ0 hrel'
      refine ⟨s, hs, A, A'' + ρ.comp A, hA, hA''.add (hρ.comp hA), hus, ?_⟩
      rw [map_add, aeval_comp, ← hus, ← hvs, sub_add_cancel]
  intro u v α β hN hu hv hα hβ hα0 hβ0 hrel
  rcases le_total β.natDegree α.natDegree with hle | hle
  · exact step u v α β hN hu hv hα hβ hα0 hβ0 hrel hle
  · obtain ⟨s, hs, A, A', hA, hA', hvs, hus⟩ :=
      step v u β α (by omega) hv hu hβ hα hβ0 hα0 hrel.symm hle
    exact ⟨s, hs, A', A, hA', hA, hus, hvs⟩

end Euclid

end Langlands.GroupScheme.Unipotent.OneDimensional
