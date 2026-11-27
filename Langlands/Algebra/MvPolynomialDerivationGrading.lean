import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Derivations of polynomial rings shifting a weighted grading -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.MvPolynomialDerivationGrading

open MvPolynomial Finsupp

variable {R : Type u} [CommRing R] {σ : Type v} (wt : σ → ℤ)

/-- A derivation sending each variable `X i` to a polynomial homogeneous of weight
`wt i + c` sends monomials of weight `n` to polynomials homogeneous of weight `n + c`. -/
theorem isWeightedHomogeneous_derivation_monomial (c : ℤ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, (D (X i)).IsWeightedHomogeneous wt (wt i + c)) (d : σ →₀ ℕ) (r : R) :
    (D (monomial d r)).IsWeightedHomogeneous wt (weight wt d + c) := by
  induction d using Finsupp.induction generalizing r with
  | zero =>
    rw [monomial_zero', ← algebraMap_eq, Derivation.map_algebraMap]
    exact isWeightedHomogeneous_zero R wt _
  | single_add i k β _ hk ih =>
    have hmon : monomial (single i k + β) r = X i ^ k * monomial β r := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    rw [hmon, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul]
    have hw : weight wt (single i k + β) + c = k • wt i + (weight wt β + c) := by
      rw [map_add, weight_single]
      abel
    refine IsWeightedHomogeneous.add ?_ ?_
    · rw [hw]
      exact ((isWeightedHomogeneous_X R wt i).pow k).mul (ih r)
    · have hk1 : (k - 1) • wt i + (wt i + c) = k • wt i + c := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Nat.add_sub_cancel, succ_nsmul]
        abel
      have h1 : (monomial β r * (k • (X i ^ (k - 1) * D (X i)))).IsWeightedHomogeneous wt
          (weight wt β + ((k - 1) • wt i + (wt i + c))) := by
        refine (isWeightedHomogeneous_monomial wt β r rfl).mul ?_
        have h2 : X i ^ (k - 1) * D (X i) ∈ weightedHomogeneousSubmodule R wt
            ((k - 1) • wt i + (wt i + c)) :=
          ((isWeightedHomogeneous_X R wt i).pow (k - 1)).mul (hD i)
        exact nsmul_mem h2 k
      convert h1 using 1
      rw [hw, hk1]
      abel

theorem isWeightedHomogeneous_derivation (c : ℤ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, (D (X i)).IsWeightedHomogeneous wt (wt i + c)) {p : MvPolynomial σ R} {n : ℤ}
    (hp : p.IsWeightedHomogeneous wt n) : (D p).IsWeightedHomogeneous wt (n + c) := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R wt _
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    rw [← hr]
    exact isWeightedHomogeneous_derivation_monomial wt c D hD d r

/-- Such a derivation maps the weight-`n` component to the weight-`n + c` component. -/
theorem weightedHomogeneousComponent_derivation (c : ℤ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, (D (X i)).IsWeightedHomogeneous wt (wt i + c)) (n : ℤ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent wt (n + c) (D p) = D (weightedHomogeneousComponent wt n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    have h1 := isWeightedHomogeneous_derivation_monomial wt c D hD d r
    rw [weightedHomogeneousComponent_of_mem h1,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial wt d r rfl)]
    by_cases h : n = weight wt d
    · rw [ite_eq_left (by rw [h]), ite_eq_left h]
    · rw [ite_eq_right (by intro h'; exact h (by linarith)), ite_eq_right h, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-- The part of a derivation shifting the weight by `c`. -/
def shiftPart (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (c : ℤ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => weightedHomogeneousComponent wt (wt i + c) (D (X i))

theorem shiftPart_X (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (c : ℤ) (i : σ) :
    shiftPart wt D c (X i) = weightedHomogeneousComponent wt (wt i + c) (D (X i)) :=
  mkDerivation_X R _ i

theorem shiftPart_isWeightedHomogeneous (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (c : ℤ) (i : σ) : (shiftPart wt D c (X i)).IsWeightedHomogeneous wt (wt i + c) := by
  rw [shiftPart_X]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- A derivation whose values on the variables only have components of weight shifted by
`-1`, `0` or `1` is the sum of its three shift parts. -/
theorem eq_shiftPart_add (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i (n : ℤ), n ≠ wt i - 1 → n ≠ wt i → n ≠ wt i + 1 →
      weightedHomogeneousComponent wt n (D (X i)) = 0) :
    D = shiftPart wt D (-1) + shiftPart wt D 0 + shiftPart wt D 1 := by
  classical
  refine derivation_ext fun i => ?_
  rw [Derivation.add_apply, Derivation.add_apply, shiftPart_X, shiftPart_X, shiftPart_X]
  conv_lhs => rw [← sum_weightedHomogeneousComponent wt (D (X i))]
  rw [finsum_eq_sum_of_support_subset (s := {wt i + -1, wt i + 0, wt i + 1})]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton, add_assoc]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    simp only [not_or] at hne
    exact hn (hD i n (by omega) (by omega) (by omega))

/-- **Lowest-component argument.** Let `s` be a polynomial whose monomials all satisfy `Q`,
annihilated by a family of derivations whose values on the variables shift the weight by at most
one. If for every nonzero polynomial whose monomials satisfy `Q` some member of the family has a
weight-lowering part not annihilating it, then `s = 0`. -/
theorem eq_zero_of_derivations {Y : Type w}
    (D : Y → Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ y i (n : ℤ), n ≠ wt i - 1 → n ≠ wt i → n ≠ wt i + 1 →
      weightedHomogeneousComponent wt n (D y (X i)) = 0)
    (Q : (σ →₀ ℕ) → Prop)
    (hnd : ∀ t : MvPolynomial σ R, t ≠ 0 → (∀ α ∈ t.support, Q α) →
      ∃ y, shiftPart wt (D y) (-1) t ≠ 0)
    (s : MvPolynomial σ R) (hs : ∀ α ∈ s.support, Q α) (hDs : ∀ y, D y s = 0) : s = 0 := by
  classical
  by_contra hs0
  obtain ⟨α₀, hα₀, hmin⟩ := Finset.exists_min_image s.support (weight wt)
    (support_nonempty.mpr hs0)
  set W := weight wt α₀
  set s₀ := weightedHomogeneousComponent wt W s
  have hlow (n : ℤ) (hn : n < W) : weightedHomogeneousComponent wt n s = 0 :=
    weightedHomogeneousComponent_eq_zero' n s fun d hd h => by
      have := hmin d hd
      omega
  have hs₀ : s₀ ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff α₀) h
    simp only [s₀, coeff_weightedHomogeneousComponent] at hc
    rw [ite_eq_left rfl] at hc
    exact (MvPolynomial.mem_support_iff.mp hα₀) (by simpa using hc)
  have hQ : ∀ α ∈ s₀.support, Q α := by
    intro α hα
    refine hs α ?_
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    intro h
    apply hα
    simp [s₀, coeff_weightedHomogeneousComponent, h]
  obtain ⟨y, hy⟩ := hnd s₀ hs₀ hQ
  apply hy
  have hsplit := eq_shiftPart_add wt (D y) (hD y)
  have hc (c : ℤ) (n : ℤ) := weightedHomogeneousComponent_derivation wt c (shiftPart wt (D y) c)
    (shiftPart_isWeightedHomogeneous wt (D y) c) n s
  have h0 : weightedHomogeneousComponent wt (W - 1) (D y s) = 0 := by rw [hDs y, map_zero]
  rw [hsplit, Derivation.add_apply, Derivation.add_apply, map_add, map_add] at h0
  have e1 := hc (-1) W
  have e2 := hc 0 (W - 1)
  have e3 := hc 1 (W - 2)
  rw [show W + -1 = W - 1 by ring] at e1
  rw [show W - 1 + 0 = W - 1 by ring, hlow (W - 1) (by omega), map_zero] at e2
  rw [show W - 2 + 1 = W - 1 by ring, hlow (W - 2) (by omega), map_zero] at e3
  rw [e1, e2, e3, add_zero, add_zero] at h0
  exact h0

end Langlands.Algebra.MvPolynomialDerivationGrading
