import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Coordinate operations for plane curves

Elementary substitution in the first coordinate, and its interaction with
partial degree, differentiation, scalar extension and evaluation.
-/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.LangWeil

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- Substitute `X^p` for the first variable, leaving the second variable fixed. -/
def planeCurveExpandFirst (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  (finSuccEquiv R 1).symm
    (Polynomial.expand (MvPolynomial (Fin 1) R) p (finSuccEquiv R 1 f))

theorem planeCurve_finSuccEquiv_map {S : Type v} [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    finSuccEquiv S 1 (map φ f) =
      Polynomial.map (map φ) (finSuccEquiv R 1 f) := by
  ext k m
  simp only [finSuccEquiv_coeff_coeff, Polynomial.coeff_map, coeff_map]

theorem planeCurve_finSuccEquiv_pderiv (f : MvPolynomial (Fin 2) R) :
    finSuccEquiv R 1 (pderiv 0 f) =
      Polynomial.derivative (finSuccEquiv R 1 f) := by
  ext k m
  simp only [finSuccEquiv_coeff_coeff, coeff_pderiv, Finsupp.cons_zero,
    Polynomial.coeff_derivative]
  have he : m.cons k + Finsupp.single (0 : Fin 2) 1 = m.cons (k + 1) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [he]
  have hc (a : MvPolynomial (Fin 1) R) (n : ℕ) :
      (a * (n : MvPolynomial (Fin 1) R)).coeff m = a.coeff m * (n : R) := by
    rw [mul_comm, ← nsmul_eq_mul, coeff_smul, nsmul_eq_mul, mul_comm]
  simpa only [Nat.cast_add, Nat.cast_one, finSuccEquiv_coeff_coeff] using
    (hc ((finSuccEquiv R 1 f).coeff (k + 1)) (k + 1)).symm

theorem planeCurve_degree_second_le_iff (f : MvPolynomial (Fin 2) R) (d : ℕ) :
    f.degreeOf 1 ≤ d ↔
      ∀ k, ((finSuccEquiv R 1 f).coeff k).degreeOf 0 ≤ d := by
  constructor
  · intro h k
    exact (degreeOf_coeff_finSuccEquiv f (0 : Fin 1) k).trans h
  · intro h
    rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro m hm
    have hc : m.tail ∈ ((finSuccEquiv R 1 f).coeff (m 0)).support := by
      rw [mem_support_coeff_finSuccEquiv, Finsupp.cons_tail]
      exact hm
    exact (monomial_le_degreeOf (0 : Fin 1) hc).trans (h (m 0))

theorem planeCurveExpandFirst_degree_first (p : ℕ)
    (f : MvPolynomial (Fin 2) R) :
    (planeCurveExpandFirst p f).degreeOf 0 = f.degreeOf 0 * p := by
  rw [← natDegree_finSuccEquiv, planeCurveExpandFirst,
    AlgEquiv.apply_symm_apply, Polynomial.natDegree_expand, natDegree_finSuccEquiv]

theorem planeCurveExpandFirst_degree_second (p : ℕ) (hp : 0 < p)
    (f : MvPolynomial (Fin 2) R) :
    (planeCurveExpandFirst p f).degreeOf 1 = f.degreeOf 1 := by
  apply le_antisymm
  · apply (planeCurve_degree_second_le_iff _ _).mpr
    intro k
    simp only [planeCurveExpandFirst, AlgEquiv.apply_symm_apply,
      Polynomial.coeff_expand hp]
    split_ifs
    · exact degreeOf_coeff_finSuccEquiv f (0 : Fin 1) _
    · simp
  · apply (planeCurve_degree_second_le_iff _ _).mpr
    intro k
    have h := degreeOf_coeff_finSuccEquiv (planeCurveExpandFirst p f) (0 : Fin 1) (k * p)
    simpa only [planeCurveExpandFirst, AlgEquiv.apply_symm_apply,
      Polynomial.coeff_expand_mul hp, Fin.succ_zero_eq_one] using h

theorem planeCurveExpandFirst_map {S : Type v} [CommRing S]
    (φ : R →+* S) (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    map φ (planeCurveExpandFirst p f) = planeCurveExpandFirst p (map φ f) := by
  apply (finSuccEquiv S 1).injective
  simp only [planeCurve_finSuccEquiv_map, planeCurveExpandFirst,
    AlgEquiv.apply_symm_apply, Polynomial.map_expand]

theorem planeCurve_eval_finSuccEquiv (f : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![x, y] f =
      Polynomial.eval x
        (Polynomial.map (eval (fun _ : Fin 1 => y)) (finSuccEquiv R 1 f)) := by
  have hv : Fin.cons x (fun _ : Fin 1 => y) = ![x, y] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hv] using eval_eq_eval_mv_eval' (fun _ : Fin 1 => y) x f

theorem planeCurveExpandFirst_eval (p : ℕ) (f : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![x, y] (planeCurveExpandFirst p f) = eval ![x ^ p, y] f := by
  rw [planeCurve_eval_finSuccEquiv, planeCurve_eval_finSuccEquiv]
  simp only [planeCurveExpandFirst, AlgEquiv.apply_symm_apply,
    Polynomial.map_expand, Polynomial.expand_eval]

theorem planeCurveExpandFirst_irreducible {F : Type u} [Field F]
    (p : ℕ) (hp : p ≠ 0) (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible
      (map (algebraMap F (AlgebraicClosure F)) (planeCurveExpandFirst p f))) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) f) := by
  rw [planeCurveExpandFirst_map] at hirr
  have h := (MulEquiv.irreducible_iff (finSuccEquiv (AlgebraicClosure F) 1)).mpr hirr
  simp only [planeCurveExpandFirst, AlgEquiv.apply_symm_apply] at h
  exact (MulEquiv.irreducible_iff (finSuccEquiv (AlgebraicClosure F) 1)).mp
    (Polynomial.of_irreducible_expand hp h)

/-- A zero first partial derivative permits contraction of the first exponents. -/
theorem planeCurve_exists_contractFirst (p : ℕ) [CharP R p] [NoZeroDivisors R]
    (hp : p ≠ 0) (f : MvPolynomial (Fin 2) R) (hf : pderiv 0 f = 0) :
    ∃ g : MvPolynomial (Fin 2) R, planeCurveExpandFirst p g = f := by
  refine ⟨(finSuccEquiv R 1).symm (Polynomial.contract p (finSuccEquiv R 1 f)), ?_⟩
  apply (finSuccEquiv R 1).injective
  simp only [planeCurveExpandFirst, AlgEquiv.apply_symm_apply]
  apply Polynomial.expand_contract p _ hp
  rw [← planeCurve_finSuccEquiv_pderiv, hf, map_zero]

/-- Apply a permutation of the field to the first coordinate. -/
def planeCurveFirstEquiv {A : Type u} (e : A ≃ A) : (Fin 2 → A) ≃ (Fin 2 → A) where
  toFun v := ![e (v 0), v 1]
  invFun v := ![e.symm (v 0), v 1]
  left_inv v := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp

theorem planeCurve_fin_two_eta {A : Type u} (v : Fin 2 → A) :
    ![v 0, v 1] = v := by
  ext i
  fin_cases i <;> rfl

/-- Frobenius expansion in one coordinate preserves the rational zero count. -/
theorem planeCurveExpandFirst_zero_count {F : Type u} [Field F] [Finite F]
    (f : MvPolynomial (Fin 2) F) :
    Nat.card {v : Fin 2 → F // eval v (planeCurveExpandFirst (ringChar F) f) = 0} =
      Nat.card {v : Fin 2 → F // eval v f = 0} := by
  let : Fact (Nat.Prime (ringChar F)) := ⟨CharP.prime_ringChar F⟩
  let e := planeCurveFirstEquiv (frobeniusEquiv F (ringChar F)).toEquiv
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro v
  change eval v (planeCurveExpandFirst (ringChar F) f) = 0 ↔
    eval ![(frobeniusEquiv F (ringChar F)) (v 0), v 1] f = 0
  rw [frobeniusEquiv_def,
    ← planeCurveExpandFirst_eval (ringChar F) f (v 0) (v 1),
    planeCurve_fin_two_eta]

/-- Extracting a Frobenius power strictly decreases a positive first degree. -/
theorem planeCurve_contractFirst_degree {F : Type u} [Field F] [Finite F]
    {f g : MvPolynomial (Fin 2) F}
    (hfg : planeCurveExpandFirst (ringChar F) g = f) (hf : 0 < f.degreeOf 0) :
    0 < g.degreeOf 0 ∧ g.degreeOf 0 < f.degreeOf 0 ∧
      g.degreeOf 1 = f.degreeOf 1 := by
  have hp := (CharP.prime_ringChar F).two_le
  have hdeg : f.degreeOf 0 = g.degreeOf 0 * ringChar F := by
    rw [← hfg, planeCurveExpandFirst_degree_first]
  have hpos : 0 < g.degreeOf 0 := by
    by_contra hn
    have hz : g.degreeOf 0 = 0 := by omega
    rw [hdeg, hz, zero_mul] at hf
    omega
  refine ⟨hpos, ?_, ?_⟩
  · rw [hdeg]
    calc
      g.degreeOf 0 = g.degreeOf 0 * 1 := (Nat.mul_one _).symm
      _ < g.degreeOf 0 * ringChar F := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  · rw [← hfg, planeCurveExpandFirst_degree_second (ringChar F) (by omega)]

end Langlands.AlgebraicGeometry.LangWeil
