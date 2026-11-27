import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Polynomial restriction under derivations transverse to a coordinate subspace -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.InvariantPolynomialRestriction

open Finsupp MvPolynomial

attribute [local instance] Classical.decEq

variable {k σ : Type*} [Field k] [CharZero k]

private def HasWeightAtLeast (w : σ → ℕ) (n : ℕ) (p : MvPolynomial σ k) : Prop :=
  ∀ m, weight w m < n → p.coeff m = 0

omit [CharZero k] in
private theorem weightBound_mul {w : σ → ℕ} {n₁ n₂ : ℕ} {p q : MvPolynomial σ k}
    (hp : HasWeightAtLeast w n₁ p) (hq : HasWeightAtLeast w n₂ q) :
    HasWeightAtLeast w (n₁ + n₂) (p * q) := by
  classical
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hsum := Finset.mem_antidiagonal.mp ha
  rw [← hsum, map_add] at hm
  by_cases h₁ : weight w a.1 < n₁
  · rw [hp _ h₁, zero_mul]
  · rw [hq _ (by omega), mul_zero]

omit [CharZero k] in
private theorem weightBound_pderiv {w : σ → ℕ} {n : ℕ} {p : MvPolynomial σ k}
    (i : σ) (h : HasWeightAtLeast w n p) :
    HasWeightAtLeast w (n - w i) (pderiv i p) := by
  intro m hm
  rw [coeff_pderiv, h (m + single i 1) ?_, zero_mul]
  rw [map_add, weight_single, one_smul]
  omega

omit [CharZero k] in
private theorem derivation_eq_sum [Fintype σ]
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (p : MvPolynomial σ k) :
    D p = ∑ j, D (X j) * pderiv j p := by
  have hApply (q : MvPolynomial σ k) :
      (∑ j, D (X j) • pderiv (R := k) j) q = ∑ j, D (X j) * pderiv j q := by
    change (∑ j, D (X j) • pderiv (R := k) j).toLinearMap q = _
    rw [Derivation.coe_sum_linearMap, LinearMap.sum_apply]
    rfl
  have h : D = ∑ j, D (X j) • pderiv j := by
    apply derivation_ext
    intro i
    rw [hApply]
    simp [pderiv_X, Pi.single_apply, mul_ite]
  exact (congrArg (fun E : Derivation k (MvPolynomial σ k) (MvPolynomial σ k) => E p) h).trans
    (hApply p)

omit [CharZero k] in
private theorem lowest_component_derivation [Fintype σ]
    {w : σ → ℕ} (hw : ∀ j, w j ≤ 1) {i : σ} (hi : w i = 1) {n : ℕ}
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (a p : MvPolynomial σ k) (ha : a.IsWeightedHomogeneous w 0)
    (h : HasWeightAtLeast w (n + 1) p) (hD : D p = 0)
    (hcoef : ∀ j, w j = 1 →
      weightedHomogeneousComponent w 0 (D (X j)) = if j = i then a else 0) :
    a * pderiv i (weightedHomogeneousComponent w (n + 1) p) = 0 := by
  classical
  let b (j : σ) := D (X j) - if j = i then a else 0
  have hb (j : σ) : HasWeightAtLeast w (w j) (b j) := by
    intro m hm
    have hm0 : weight w m = 0 := by have := hw j; omega
    have hj : w j = 1 := by have := hw j; omega
    have heq := congrArg (fun q : MvPolynomial σ k => q.coeff m) (hcoef j hj)
    rw [coeff_weightedHomogeneousComponent, hm0, ite_eq_left rfl] at heq
    change (D (X j) - (if j = i then a else 0)).coeff m = 0
    rw [coeff_sub, heq, sub_self]
  have hSum : D p = a * pderiv i p + ∑ j, b j * pderiv j p := by
    rw [derivation_eq_sum]
    simp only [b, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    abel
  have hTerms : HasWeightAtLeast w (n + 1) (∑ j, b j * pderiv j p) := by
    intro m hm
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply weightBound_mul (hb j) (weightBound_pderiv j h)
    have := hw j
    omega
  let q := weightedHomogeneousComponent w (n + 1) p
  have hRest : HasWeightAtLeast w (n + 2) (p - q) := by
    intro m hm
    rw [coeff_sub]
    by_cases hEq : weight w m = n + 1
    · simp [q, coeff_weightedHomogeneousComponent, hEq]
    · rw [h m (by omega)]
      simp [q, coeff_weightedHomogeneousComponent, hEq]
  have hRestDeriv : HasWeightAtLeast w (n + 1) (a * pderiv i (p - q)) := by
    have hA : HasWeightAtLeast w 0 a := fun _ hlt => (Nat.not_lt_zero _ hlt).elim
    simpa [hi] using weightBound_mul hA (weightBound_pderiv i hRest)
  have hHomDeriv : (pderiv i q).IsWeightedHomogeneous w n := by
    intro m hm
    rw [coeff_pderiv] at hm
    have hDegree : weight w (m + single i 1) = n + 1 :=
      weightedHomogeneousComponent_isWeightedHomogeneous (n + 1) p
        (left_ne_zero_of_mul hm)
    simpa [map_add, weight_single, hi] using hDegree
  have hHom := ha.mul hHomDeriv
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hm : weight w m = n
  · have hlt : weight w m < n + 1 := by omega
    have hpDer := congrArg (fun q : MvPolynomial σ k => q.coeff m) (hSum.symm.trans hD)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hTerms m hlt, add_zero,
      AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at hpDer
    have hRestCoeff := hRestDeriv m hlt
    rw [map_sub, mul_sub, coeff_sub, hpDer, zero_sub, neg_eq_zero] at hRestCoeff
    exact hRestCoeff
  · exact not_not.mp (mt (fun h => by simpa using hHom h) hm)

/-- An invariant polynomial is determined by its restriction to the variables of weight zero
when, along that subspace, the derivations supply a nonzero multiple of each normal partial
derivative. The weights are zero on retained variables and one on the normal variables. -/
def InvariantPolynomialRestrictionStatement (k σ : Type*) [Field k] [CharZero k]
    [Fintype σ] : Prop :=
  ∀ (w : σ → ℕ), (∀ j, w j ≤ 1) → ∀ p : MvPolynomial σ k,
    weightedHomogeneousComponent w 0 p = 0 →
    (∀ i, w i = 1 → ∃ (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
      (a : MvPolynomial σ k), a ≠ 0 ∧ a.IsWeightedHomogeneous w 0 ∧ D p = 0 ∧
        ∀ j, w j = 1 →
          weightedHomogeneousComponent w 0 (D (X j)) = if j = i then a else 0) →
    p = 0

theorem invariantPolynomialRestriction [Fintype σ] :
    InvariantPolynomialRestrictionStatement k σ := by
  classical
  intro w hw p hzero hD
  by_contra hp
  have hExists : ∃ n, ∃ m, weight w m = n ∧ p.coeff m ≠ 0 := by
    obtain ⟨m, hm⟩ := not_forall.mp (mt MvPolynomial.eq_zero_iff.mpr hp)
    exact ⟨weight w m, m, rfl, hm⟩
  let n := Nat.find hExists
  obtain ⟨m, hm, hCoeff⟩ := Nat.find_spec hExists
  have hPos : 0 < n := by
    by_contra! hn
    have hm0 : weight w m = 0 := hm.trans (Nat.eq_zero_of_le_zero hn)
    have heq := congrArg (fun q : MvPolynomial σ k => q.coeff m) hzero
    simp only [coeff_weightedHomogeneousComponent, hm0, ite_true,
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at heq
    exact hCoeff heq
  have hBound : HasWeightAtLeast w n p := by
    intro s hs
    by_contra h
    have hle := Nat.find_min' hExists ⟨s, rfl, h⟩
    exact (not_lt_of_ge hle) hs
  obtain ⟨i, hi, hmi⟩ : ∃ i, w i = 1 ∧ m i ≠ 0 := by
    by_contra! hNone
    have hWeight : weight w m = 0 := by
      rw [weight_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hwj : w j ≠ 1 := fun h => (Finsupp.mem_support_iff.mp hj) (hNone j h)
      have : w j = 0 := by have := hw j; omega
      rw [this, smul_zero]
    rw [hWeight] at hm
    omega
  obtain ⟨D, a, ha, haHom, hInv, hGenerator⟩ := hD i hi
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hPos.ne'
  have hVanishing := lowest_component_derivation hw hi D a p haHom
    (hr ▸ hBound) hInv hGenerator
  have hDerivative := (mul_eq_zero.mp hVanishing).resolve_left ha
  have hValue := congrArg (fun q : MvPolynomial σ k => q.coeff (m - single i 1)) hDerivative
  have hmDegree : weight w m = r + 1 := hm.trans hr
  rw [coeff_pderiv, sub_add_single_one_cancel hmi,
    coeff_weightedHomogeneousComponent, hmDegree, ite_eq_left rfl] at hValue
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hValue
  let exponent : σ →₀ ℕ := m - single i 1
  have hScalar : (exponent i : k) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (exponent i)
  exact hCoeff ((mul_eq_zero.mp hValue).resolve_right hScalar)

end Langlands.Algebra.InvariantPolynomialRestriction
