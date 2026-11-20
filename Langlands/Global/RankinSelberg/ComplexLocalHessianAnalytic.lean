import Langlands.Global.RankinSelberg.ComplexLocalWhittakerEllipticChart
import Langlands.Analysis.ScalarEllipticAnalyticityProof

/-! # Analyticity of eigenfunctions of the complex matrix Hessian sum -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Analysis

variable (n : ℕ)
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "d" => Fintype.card (Bool × Fin n × Fin n)

private def shiftedComplexEllipticOperator (c : ℂ) : CoordinateScalarOperator M d 2 :=
  { complexEllipticChartOperator n with
    coefficient := fun k w h =>
      if k.val = 0 then -c else (complexEllipticChartOperator n).coefficient k w h }

private theorem shiftedComplexEllipticOperator_action (c : ℂ) (f : M → ℂ) (h : M) :
    (shiftedComplexEllipticOperator n c).action f h =
      complexCoordinateHessianSum f h - c * f h := by
  rw [← complexEllipticChartOperator_action]
  let D := complexEllipticChartOperator n
  change
    (∑ k : Fin 3, ∑ w : Fin k.val → Fin d,
      (if k.val = 0 then -c else D.coefficient k w h) *
        iteratedFDeriv ℝ k.val f h (fun j => D.basis (w j))) =
    (∑ k : Fin 3, ∑ w : Fin k.val → Fin d, D.coefficient k w h *
        iteratedFDeriv ℝ k.val f h (fun j => D.basis (w j))) - c * f h
  have hzero : (complexEllipticChartOperator n).coefficient 0 = 0 := by
    funext w y
    simp [complexEllipticChartOperator]
  change D.coefficient 0 = 0 at hzero
  simp [Fin.sum_univ_three, hzero, sub_eq_add_neg, add_assoc, add_comm]

private theorem shiftedComplexEllipticOperator_analytic (c : ℂ) :
    (shiftedComplexEllipticOperator n c).AnalyticCoefficientsOn Set.univ := by
  intro k w
  by_cases hk : k.val = 0
  · simp only [shiftedComplexEllipticOperator, hk, ite_true]
    exact analyticOnNhd_const
  · simp only [shiftedComplexEllipticOperator, hk, ite_false]
    exact complexEllipticChartOperator_analytic n k w

private theorem shiftedComplexEllipticOperator_elliptic (c : ℂ) :
    (shiftedComplexEllipticOperator n c).IsEllipticOn {h : M | IsUnit h} := by
  intro h hh ξ hξ
  simp only [CoordinateScalarOperator.principalSymbol, shiftedComplexEllipticOperator,
    Fin.val_last, OfNat.ofNat_ne_zero, ite_false]
  exact complexEllipticChartOperator_elliptic n h hh ξ hξ

/-- Smooth eigenfunctions of the Hessian sum are analytic on the invertible locus. -/
theorem analyticOnNhd_of_complexCoordinateHessianSum_eq (c : ℂ) {f : M → ℂ}
    (hf : ContDiffOn ℝ ∞ f {h | IsUnit h})
    (heq : ∀ h, IsUnit h → complexCoordinateHessianSum f h = c * f h) :
    AnalyticOnNhd ℝ f {h | IsUnit h} :=
  scalarEllipticAnalyticity M d 2 (shiftedComplexEllipticOperator n c) _ f
    Langlands.Archimedean.isOpen_setOf_isUnit_matrix
    ((shiftedComplexEllipticOperator_analytic n c).mono (Set.subset_univ _))
    (shiftedComplexEllipticOperator_elliptic n c) hf fun h hh => by
      rw [shiftedComplexEllipticOperator_action, heq h hh, sub_self]

end Langlands.Global.RankinSelbergGlobal
