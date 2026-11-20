import Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransport
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerMatrixDifferential

/-! # The complex coefficient square operator as an elliptic coordinate operator -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Analysis Langlands.Archimedean.ComplexLocalCasimir Module

variable (n : ℕ)

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "J" => Bool × Fin n × Fin n
local notation "d" => Fintype.card J
local notation "I" => Fin d

/-- The real matrix basis reindexed by its dimension. -/
def complexEllipticBasis : Basis I ℝ M :=
  (matrixRealBasis n).reindex (Fintype.equivFin J)

private def fieldCoordinate (i j : I) : M →L[ℝ] ℝ :=
  ((complexEllipticBasis n).coord j).toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℝ M).flip (complexEllipticBasis n i))

private theorem fieldCoordinate_apply (i j : I) (h : M) :
    fieldCoordinate n i j h = (complexEllipticBasis n).repr (h * complexEllipticBasis n i) j :=
  rfl

private def secondCoefficient (p q : I) (h : M) : ℂ :=
  ((∑ i : I, fieldCoordinate n i p h * fieldCoordinate n i q h : ℝ) : ℂ)

/-- The matrix-chart operator with the right-coordinate Hessian coefficients
and zero lower-order coefficients. -/
def complexEllipticChartOperator : CoordinateScalarOperator M d 2 where
  basis := complexEllipticBasis n
  coefficient k w h :=
    if hk : 1 < k.val then secondCoefficient n (w ⟨0, lt_trans zero_lt_one hk⟩) (w ⟨1, hk⟩) h
    else 0

private theorem sum_words_two {A : Type*} [AddCommMonoid A] (f : I → I → A) :
    (∑ w : Fin 2 → I, f (w 0) (w 1)) = ∑ p : I, ∑ q : I, f p q := by
  calc
    _ = ∑ p : I × I, f p.1 p.2 :=
      Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => I)) (fun p : I × I => f p.1 p.2)
    _ = _ := Fintype.sum_prod_type _

private theorem sum_rotate {A : Type*} [AddCommMonoid A] (f : I → I → I → A) :
    (∑ p : I, ∑ q : I, ∑ i : I, f i p q) = ∑ i : I, ∑ p : I, ∑ q : I, f i p q := by
  calc
    _ = ∑ p : I, ∑ i : I, ∑ q : I, f i p q :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem sum_fieldCoordinates (i : I) (h : M) :
    (∑ j : I, fieldCoordinate n i j h • complexEllipticBasis n j) = h * complexEllipticBasis n i := by
  simp only [fieldCoordinate_apply, Basis.sum_repr]

private theorem hessian_expand (i : I) (h : M) (T : M →L[ℝ] M →L[ℝ] ℂ) :
    T (h * complexEllipticBasis n i) (h * complexEllipticBasis n i) =
      ∑ p : I, ∑ q : I,
        (fieldCoordinate n i p h : ℂ) * (fieldCoordinate n i q h : ℂ) *
          T (complexEllipticBasis n p) (complexEllipticBasis n q) := by
  calc
    _ = T (∑ p, fieldCoordinate n i p h • complexEllipticBasis n p)
        (∑ q, fieldCoordinate n i q h • complexEllipticBasis n q) := by
      rw [sum_fieldCoordinates]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        Complex.real_smul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring

/-- The differential action of the actual coordinate operator is the
Hessian sum obtained from the Whittaker square operator. -/
theorem complexEllipticChartOperator_action (f : M → ℂ) (h : M) :
    (complexEllipticChartOperator n).action f h = complexCoordinateHessianSum f h := by
  let e := complexEllipticBasis n
  let T := fderiv ℝ (fderiv ℝ f) h
  change (∑ k : Fin 3, ∑ w : Fin k.val → I,
    (if hk : 1 < k.val then secondCoefficient n (w ⟨0, lt_trans zero_lt_one hk⟩) (w ⟨1, hk⟩) h
      else 0) * iteratedFDeriv ℝ k.val f h (fun j => e (w j))) = _
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.lt_irrefl, Nat.not_lt_zero,
    Nat.one_lt_two, dite_false, dite_true, zero_mul, Finset.sum_const_zero, zero_add,
    iteratedFDeriv_two_apply]
  change (∑ w : Fin 2 → I, secondCoefficient n (w 0) (w 1) h * T (e (w 0)) (e (w 1))) = _
  rw [sum_words_two n (fun p q => secondCoefficient n p q h * T (e p) (e q))]
  have hReindex : complexCoordinateHessianSum f h = ∑ i : I, T (h * e i) (h * e i) := by
    simpa only [e, T, complexCoordinateHessianSum, complexEllipticBasis, Basis.reindex_apply,
      Equiv.symm_apply_apply] using
      Equiv.sum_comp (Fintype.equivFin J) (fun i : I => T (h * e i) (h * e i))
  rw [hReindex]
  calc
    _ = ∑ i : I, ∑ p : I, ∑ q : I,
        (fieldCoordinate n i p h : ℂ) * (fieldCoordinate n i q h : ℂ) * T (e p) (e q) := by
      simp only [secondCoefficient, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
      exact sum_rotate n _
    _ = _ := Finset.sum_congr rfl fun i _ => (hessian_expand n i h T).symm

/-- All coefficients of the coordinate operator are analytic on the
matrix coordinate space. -/
theorem complexEllipticChartOperator_analytic :
    (complexEllipticChartOperator n).AnalyticCoefficientsOn Set.univ := by
  intro k w
  by_cases hk : 1 < k.val
  · simp only [complexEllipticChartOperator, hk, dite_true]
    unfold secondCoefficient
    have hlin (p q : I) : AnalyticOnNhd ℝ (fun h => (fieldCoordinate n p q h : ℂ)) Set.univ :=
      (Complex.ofRealCLM.comp (fieldCoordinate n p q)).analyticOnNhd _
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    exact Finset.analyticOnNhd_fun_sum _ fun i _ => (hlin i _).mul (hlin i _)
  · simp only [complexEllipticChartOperator, hk, dite_false]
    exact analyticOnNhd_const

/-- The chart operator is elliptic on the open set of invertible matrices. -/
theorem complexEllipticChartOperator_elliptic :
    (complexEllipticChartOperator n).IsEllipticOn {h : M | IsUnit h} := by
  intro h hh ξ hξ
  let hUnit : G := hh.unit
  let e := complexEllipticBasis n
  change (∑ w : Fin 2 → I, secondCoefficient n (w 0) (w 1) h *
    ∏ j : Fin 2, (ξ (e (w j)) : ℂ)) ≠ 0
  simp only [Fin.prod_univ_two]
  rw [sum_words_two n (fun p q => secondCoefficient n p q h *
    ((ξ (e p) : ℂ) * (ξ (e q) : ℂ)))]
  have hscale (i : I) : (∑ p, (fieldCoordinate n i p h : ℂ) * (ξ (e p) : ℂ)) =
      (ξ (h * e i) : ℂ) := by
    rw [← sum_fieldCoordinates n i h]
    simp only [map_sum, map_smul, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul]
    rfl
  have heq : (∑ p, ∑ q, secondCoefficient n p q h *
      ((ξ (e p) : ℂ) * (ξ (e q) : ℂ))) = (↑(∑ i : I, ξ (h * e i) ^ 2) : ℂ) := by
    calc
      _ = ∑ i : I, ∑ p : I, ∑ q : I, (fieldCoordinate n i p h : ℂ) *
          (fieldCoordinate n i q h : ℂ) * ((ξ (e p) : ℂ) * (ξ (e q) : ℂ)) := by
        simp only [secondCoefficient, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
        exact sum_rotate n _
      _ = ∑ i : I, (∑ p : I, (fieldCoordinate n i p h : ℂ) * (ξ (e p) : ℂ)) ^ 2 := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => ?_
        ring
      _ = _ := by simp only [hscale, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [heq]
  have hpos : 0 < ∑ i : I, ξ (h * e i) ^ 2 := by
    have hp := complexCoordinateHessianSymbol_pos hUnit ξ hξ
    have he : (∑ j : J, ξ (h * matrixRealBasis n j) ^ 2) = ∑ i : I, ξ (h * e i) ^ 2 := by
      simpa only [e, complexEllipticBasis, Basis.reindex_apply, Equiv.symm_apply_apply] using
        Equiv.sum_comp (Fintype.equivFin J) (fun i : I => ξ (h * e i) ^ 2)
    rw [← he]
    exact hp
  exact_mod_cast hpos.ne'

end Langlands.Global.RankinSelbergGlobal
