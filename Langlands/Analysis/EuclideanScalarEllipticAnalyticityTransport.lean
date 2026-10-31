import Langlands.Analysis.CoordinateScalarTransport
import Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransportStatement
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Analytic.Linear

/-! # Scalar elliptic analytic regularity through the actual finite basis -/

noncomputable section
universe v w
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

namespace CoordinateScalarOperator

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] {d r : ℕ}

/-- Every iterated derivative changes variables through a continuous linear equivalence. -/
theorem iteratedFDeriv_comp_equiv (e : E ≃L[ℝ] G) (F : E → ℂ)
    (k : ℕ) (y : G) (vectors : Fin k → E) :
    iteratedFDeriv ℝ k (F ∘ e.symm) y (fun j => e (vectors j)) =
      iteratedFDeriv ℝ k F (e.symm y) vectors := by
  have h := e.symm.iteratedFDerivWithin_comp_right F
    uniqueDiffOn_univ (Set.mem_univ (e.symm y)) k
  have heval := congrArg (fun T => T (fun j => e (vectors j))) h
  simpa [iteratedFDerivWithin_univ] using heval

/-- The full differential expression, including every lower order, is unchanged. -/
theorem transport_action (D : CoordinateScalarOperator E d r) (e : E ≃L[ℝ] G)
    (F : E → ℂ) (y : G) :
    (D.transport e).action (F ∘ e.symm) y = D.action F (e.symm y) := by
  simp only [action, transport_coefficient, transport_basis, iteratedFDeriv_comp_equiv]

/-- The actual highest-order symbol changes by the ordinary covector pullback. -/
theorem transport_principalSymbol (D : CoordinateScalarOperator E d r)
    (e : E ≃L[ℝ] G) (y : G) (ξ : G →L[ℝ] ℝ) :
    (D.transport e).principalSymbol y ξ =
      D.principalSymbol (e.symm y) (ξ.comp e.toContinuousLinearMap) := by
  simp only [principalSymbol, transport_coefficient, transport_basis,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- The actual analytic coefficient functions compose with the inverse equivalence. -/
theorem transport_analyticCoefficients (D : CoordinateScalarOperator E d r)
    (e : E ≃L[ℝ] G) {S : Set E} (h : D.AnalyticCoefficientsOn S) :
    (D.transport e).AnalyticCoefficientsOn (e.symm ⁻¹' S) := by
  intro k word
  exact (h k word).comp (e.symm.analyticOnNhd _) (fun _ hy => hy)

/-- Ellipticity is preserved because pullback by an equivalence preserves nonzero covectors. -/
theorem transport_isElliptic (D : CoordinateScalarOperator E d r)
    (e : E ≃L[ℝ] G) {S : Set E} (h : D.IsEllipticOn S) :
    (D.transport e).IsEllipticOn (e.symm ⁻¹' S) := by
  intro y hy ξ hξ
  rw [transport_principalSymbol]
  apply h (e.symm y) hy
  intro hzero
  apply hξ
  ext z
  have hz := congrArg (fun η : E →L[ℝ] ℝ => η (e.symm z)) hzero
  simpa using hz

/-- The actual basis coordinate map sends each original basis vector to the canonical one. -/
theorem euclideanCoordinates_basis (D : CoordinateScalarOperator E d r) (i : Fin d) :
    D.euclideanCoordinates (D.basis i) =
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i := by
  ext j
  simp [euclideanCoordinates, Finsupp.single_apply, eq_comm]

/-- The transported operator has exactly the canonical Euclidean basis. -/
theorem toEuclidean_basis (D : CoordinateScalarOperator E d r) :
    D.toEuclidean.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis := by
  ext1 i
  exact D.euclideanCoordinates_basis i

end CoordinateScalarOperator

/-- Canonical Euclidean scalar regularity implies the unchanged generic assertion. -/
theorem euclideanScalarEllipticAnalyticityTransport
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) :
    EuclideanScalarEllipticAnalyticityTransportStatement E d r := by
  intro hEuclidean D S F hS hcoeff hell hF heqn
  let e := D.euclideanCoordinates
  let T : Set (EuclideanSpace ℝ (Fin d)) := e.symm ⁻¹' S
  have hT : IsOpen T := hS.preimage e.symm.continuous
  have hF' : ContDiffOn ℝ ∞ (F ∘ e.symm) T :=
    hF.comp e.symm.contDiff.contDiffOn (fun _ hy => hy)
  have heqn' : ∀ y ∈ T, D.toEuclidean.action (F ∘ e.symm) y = 0 := by
    intro y hy
    rw [CoordinateScalarOperator.toEuclidean, D.transport_action e F y]
    exact heqn (e.symm y) hy
  have han : AnalyticOnNhd ℝ (F ∘ e.symm) T :=
    hEuclidean D.toEuclidean T (F ∘ e.symm) D.toEuclidean_basis hT
      (D.transport_analyticCoefficients e hcoeff) (D.transport_isElliptic e hell)
      hF' heqn'
  intro x hx
  have hx' : e x ∈ T := by
    change e.symm (e x) ∈ S
    simpa using hx
  have h := (han (e x) hx').comp (e.analyticAt x)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h

example : ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ),
    EuclideanScalarEllipticAnalyticityTransportStatement E d r :=
  @euclideanScalarEllipticAnalyticityTransport

end Langlands.Analysis
