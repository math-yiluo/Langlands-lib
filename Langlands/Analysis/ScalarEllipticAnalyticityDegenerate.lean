import Langlands.Analysis.ScalarEllipticAnalyticityDegenerateStatement
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Zero dimension and zero order for scalar elliptic analytic regularity -/

noncomputable section
universe v
open scoped ContDiff Topology
set_option autoImplicit false

namespace Langlands.Analysis

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a zero space every function is constant and hence analytic. -/
theorem scalarEllipticAnalyticity_of_subsingleton [Subsingleton E] (d r : ℕ) :
    ScalarEllipticAnalyticityStatement E d r := by
  intro _ S F _ _ _ _ _
  have hconstant : F = fun _ => F 0 :=
    funext (fun x => congrArg F (Subsingleton.elim x 0))
  rw [hconstant]
  exact analyticOnNhd_const

/-- A given empty actual basis makes the original normed space a zero space. -/
theorem scalarEllipticAnalyticity_dimension_zero (r : ℕ) :
    ScalarEllipticAnalyticityStatement E 0 r := by
  intro D S F hS hcoeff hell hF heqn
  let : Subsingleton E := D.basis.equivFun.injective.subsingleton
  exact scalarEllipticAnalyticity_of_subsingleton E 0 r D S F
    hS hcoeff hell hF heqn

/-- At order zero, in positive dimension ellipticity forces the solution to vanish. -/
theorem scalarEllipticAnalyticity_order_zero (d : ℕ) :
    ScalarEllipticAnalyticityStatement E d 0 := by
  cases d with
  | zero => exact scalarEllipticAnalyticity_dimension_zero E 0
  | succ d =>
    intro D S F hS _ hell _ heqn
    let i : Fin (d + 1) := 0
    let ξ : E →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp D.basis.equivFunL.toContinuousLinearMap
    have hξbasis : ξ (D.basis i) = 1 := by
      change D.basis.equivFun (D.basis i) i = 1
      simp [Module.Basis.equivFun_self]
    have hξ : ξ ≠ 0 := by
      intro hzero
      have h := congrArg (fun η : E →L[ℝ] ℝ => η (D.basis i)) hzero
      rw [hξbasis] at h
      norm_num at h
    have hzero : ∀ x ∈ S, F x = 0 := by
      intro x hx
      have hsymbol := hell x hx ξ hξ
      have heq := heqn x hx
      simp [CoordinateScalarOperator.principalSymbol] at hsymbol
      simp [CoordinateScalarOperator.action] at heq
      exact heq.resolve_left hsymbol
    intro x hx
    apply (analyticAt_const : AnalyticAt ℝ (fun _ : E => (0 : ℂ)) x).congr
    filter_upwards [hS.mem_nhds hx] with y hy
    exact (hzero y hy).symm

/-- Scalar elliptic analytic regularity holds when dimension or order is zero. -/
theorem scalarEllipticAnalyticityDegenerate :
    ScalarEllipticAnalyticityDegenerateStatement E :=
  ⟨scalarEllipticAnalyticity_dimension_zero E, scalarEllipticAnalyticity_order_zero E⟩

example : ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ScalarEllipticAnalyticityDegenerateStatement E :=
  @scalarEllipticAnalyticityDegenerate

end Langlands.Analysis
