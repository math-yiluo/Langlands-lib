import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Lattice.Fold

/-! # Principal parts and polynomial curves in separated-variable kernels -/

noncomputable section

universe u v

open Polynomial
open scoped BigOperators

namespace Langlands.GroupScheme.Unipotent

variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]

/-- The highest-degree terms of a separated-variable polynomial have no
nonzero common zero over the coefficient field. -/
def HasAnisotropicPrincipalPart (f : ι → k[X]) : Prop :=
  ∀ b : ι → k, (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0 →
    b = 0

/-- A nonconstant polynomial tuple in a separated-variable kernel gives a
nonzero zero of the principal part when all coordinate degrees are positive. -/
theorem exists_principalPart_zero_of_sum_comp_eq_zero_of_positive
    (f φ : ι → k[X]) (hf : ∀ i, 0 < (f i).natDegree)
    (hφ : ∃ i, 0 < (φ i).natDegree) (h : ∑ i, (f i).comp (φ i) = 0) :
    ∃ b : ι → k, b ≠ 0 ∧
      (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hφ
  let : Nonempty ι := ⟨i₀⟩
  let d : ι → ℕ := fun i => (f i).natDegree * (φ i).natDegree
  let N : ℕ := Finset.univ.sup d
  have hd (i : ι) : d i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos (hf i₀) hi₀) (hd i₀)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty d
  have hjd : d j = N := hj.symm
  let b : ι → k := fun i => if d i = N then (φ i).leadingCoeff else 0
  have hb : b ≠ 0 := by
    intro hb
    have hφj : (φ j).natDegree ≠ 0 := by
      intro hz
      have hz' : d j = 0 := by dsimp [d]; rw [hz, Nat.mul_zero]
      have : N = 0 := hj.trans hz'
      omega
    have hb' : b j = 0 := congrFun hb j
    have : (φ j).leadingCoeff = 0 := by
      rw [show b j = (φ j).leadingCoeff from ite_eq_left hjd] at hb'
      exact hb'
    exact (Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hφj))) this
  have hcoeff (i : ι) :
      (f i).leadingCoeff * b i ^ (f i).natDegree =
        ((f i).comp (φ i)).coeff N := by
    by_cases hi : d i = N
    · have hφi : (φ i).natDegree ≠ 0 := by
        intro hz
        have : N = 0 := by simpa [d, hz] using hi.symm
        omega
      have hdeg : ((f i).comp (φ i)).natDegree = N := by
        rw [Polynomial.natDegree_comp]
        exact hi
      rw [show b i = (φ i).leadingCoeff from ite_eq_left hi,
        ← Polynomial.leadingCoeff_comp hφi, ← hdeg, Polynomial.coeff_natDegree]
    · have hlt : ((f i).comp (φ i)).natDegree < N := by
        rw [Polynomial.natDegree_comp]
        exact lt_of_le_of_ne (hd i) hi
      rw [show b i = 0 from ite_eq_right hi,
        zero_pow (Nat.ne_of_gt (hf i)), mul_zero,
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  refine ⟨b, hb, ?_⟩
  calc
    (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) =
        (∑ i, (f i).comp (φ i)).coeff N := by
      simp only [Polynomial.finsetSum_coeff]
      exact Finset.sum_congr rfl fun i _ => hcoeff i
    _ = 0 := by rw [h, Polynomial.coeff_zero]

private theorem leadingCoeff_mul_zero_pow_natDegree (p : k[X]) (hp : p.coeff 0 = 0) :
    p.leadingCoeff * (0 : k) ^ p.natDegree = 0 := by
  by_cases hd : p.natDegree = 0
  · have hl : p.leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, hd, hp]
    rw [hl, zero_mul]
  · rw [zero_pow hd, mul_zero]

/-- Zero coordinate polynomials are allowed when every constant coefficient
vanishes. A nonconstant kernel curve still yields a nonzero principal zero. -/
theorem exists_principalPart_zero_of_sum_comp_eq_zero
    (f φ : ι → k[X]) (hf : ∀ i, (f i).coeff 0 = 0)
    (hφ : ∃ i, 0 < (φ i).natDegree) (h : ∑ i, (f i).comp (φ i) = 0) :
    ∃ b : ι → k, b ≠ 0 ∧
      (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0 := by
  classical
  by_cases hd : ∀ i, 0 < (f i).natDegree
  · exact exists_principalPart_zero_of_sum_comp_eq_zero_of_positive f φ hd hφ h
  · obtain ⟨j, hj⟩ := not_forall.mp hd
    have hjd : (f j).natDegree = 0 := by omega
    have hjf : f j = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hjd, hf j, Polynomial.C_0]
    let b : ι → k := fun i => if i = j then 1 else 0
    refine ⟨b, ?_, ?_⟩
    · intro hb
      have hb' : b j = 0 := congrFun hb j
      have hb'' : (1 : k) = 0 := by simpa only [b, ite_true] using hb'
      exact one_ne_zero hb''
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = j
      · subst i
        rw [hjf, Polynomial.leadingCoeff_zero, zero_mul]
      · rw [show b i = 0 from ite_eq_right hi]
        exact leadingCoeff_mul_zero_pow_natDegree (f i) (hf i)

/-- An anisotropic principal part forces every polynomial curve in its
separated-variable zero locus to have constant coordinates. -/
theorem HasAnisotropicPrincipalPart.natDegree_eq_zero_of_sum_comp_eq_zero
    {f : ι → k[X]} (ha : HasAnisotropicPrincipalPart f)
    (hf : ∀ i, (f i).coeff 0 = 0) (φ : ι → k[X])
    (h : ∑ i, (f i).comp (φ i) = 0) (i : ι) : (φ i).natDegree = 0 := by
  by_contra hi
  obtain ⟨b, hb, hz⟩ := exists_principalPart_zero_of_sum_comp_eq_zero f φ hf
    ⟨i, Nat.pos_of_ne_zero hi⟩ h
  exact hb (ha b hz)

/-- Every coordinate of a polynomial curve in such a zero locus equals its
constant coefficient. -/
theorem HasAnisotropicPrincipalPart.eq_C_of_sum_comp_eq_zero
    {f : ι → k[X]} (ha : HasAnisotropicPrincipalPart f)
    (hf : ∀ i, (f i).coeff 0 = 0) (φ : ι → k[X])
    (h : ∑ i, (f i).comp (φ i) = 0) :
    φ = fun i => Polynomial.C ((φ i).coeff 0) := by
  funext i
  exact Polynomial.eq_C_of_natDegree_eq_zero
    (ha.natDegree_eq_zero_of_sum_comp_eq_zero hf φ h i)

end Langlands.GroupScheme.Unipotent
