import Langlands.Global.ArchimedeanCartanPolynomialCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Coefficient analyticity for the explicit Cartan recurrence -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem analyticAt_cartanMovingField (i : CartanBasisIndex K n)
    (x : ArchimedeanMatrix K n) :
    AnalyticAt ℝ (cartanMatrixField K n i) x :=
  ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
    (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))).analyticAt x

private theorem analyticAt_directionalCoefficient
    (a : ArchimedeanMatrix K n → ℂ)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n)
    (x : ArchimedeanMatrix K n) (ha : AnalyticAt ℝ a x) (hV : AnalyticAt ℝ V x) :
    AnalyticAt ℝ (fun y => fderiv ℝ a y (V y)) x :=
  ((ContinuousLinearMap.apply ℝ ℂ : ArchimedeanMatrix K n →L[ℝ]
    (ArchimedeanMatrix K n →L[ℝ] ℂ) →L[ℝ] ℂ).analyticAt_bilinear _).comp
      (hV.prod ha.fderiv)

private theorem analyticOnNhd_cartanCoefficientExtend {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (ha : ∀ k w, AnalyticOnNhd ℝ (a k w) Set.univ)
    (k : ℕ) (w : Fin k → Fin (cartanCoordinateDimension K n)) :
    AnalyticOnNhd ℝ (cartanCoefficientExtend K n a k w) Set.univ := by
  intro x hx
  change AnalyticAt ℝ (fun y => if h : k ≤ r then a ⟨k, Nat.lt_succ_of_le h⟩ w y else 0) x
  by_cases h : k ≤ r
  · simp only [dite_eq_left h]
    exact ha ⟨k, Nat.lt_succ_of_le h⟩ w x hx
  · simp only [dite_eq_right h]
    exact analyticAt_const

private theorem analyticOnNhd_cartanPrependCoefficient {r : ℕ}
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n)
    (hV : AnalyticOnNhd ℝ V Set.univ)
    (a : CartanCoordinateCoefficients K n r)
    (ha : ∀ k w, AnalyticOnNhd ℝ (a k w) Set.univ)
    (k : ℕ) (w : Fin k → Fin (cartanCoordinateDimension K n)) :
    AnalyticOnNhd ℝ (cartanPrependCoefficient K n a V k w) Set.univ := by
  cases k with
  | zero => exact analyticOnNhd_const
  | succ k =>
    intro x hx
    exact (analyticOnNhd_cartanCoefficientExtend K n a ha k (fun j => w j.succ) x hx).mul
      ((Complex.ofRealCLM.analyticAt _).comp
        (((cartanCoordinateFunctional K n (w 0)).analyticAt _).comp (hV x hx)))

theorem analyticOnNhd_cartanLeftDirectionalCoefficients {r : ℕ}
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n)
    (hV : AnalyticOnNhd ℝ V Set.univ)
    (a : CartanCoordinateCoefficients K n r)
    (ha : ∀ k w, AnalyticOnNhd ℝ (a k w) Set.univ) :
    ∀ k w, AnalyticOnNhd ℝ (cartanLeftDirectionalCoefficients K n a V k w) Set.univ := by
  intro k w x hx
  change AnalyticAt ℝ (fun y =>
    (if h : k.val ≤ r then fderiv ℝ (a ⟨k.val, Nat.lt_succ_of_le h⟩ w) y (V y) else 0) +
      cartanPrependCoefficient K n a V k.val w y) x
  apply AnalyticAt.add _ (analyticOnNhd_cartanPrependCoefficient K n V hV a ha k.val w x hx)
  by_cases h : k.val ≤ r
  · simp only [dite_eq_left h]
    exact analyticAt_directionalCoefficient K n _ V x (ha ⟨k.val, Nat.lt_succ_of_le h⟩ w x hx) (hV x hx)
  · simp only [dite_eq_right h]
    exact analyticAt_const

private theorem analyticOnNhd_cartanSquareSumCoefficients {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (ha : ∀ k w, AnalyticOnNhd ℝ (a k w) Set.univ) :
    ∀ k w, AnalyticOnNhd ℝ (cartanSquareSumCoefficients K n a k w) Set.univ := by
  intro k w x hx
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticOnNhd_cartanLeftDirectionalCoefficients K n (cartanMatrixField K n i)
    (fun y _ => analyticAt_cartanMovingField K n i y) _
    (analyticOnNhd_cartanLeftDirectionalCoefficients K n (cartanMatrixField K n i)
      (fun y _ => analyticAt_cartanMovingField K n i y) a ha) k w x hx

/-- Every actual iterate coefficient is real analytic on the full ambient matrix space. -/
theorem cartanIterateCoefficients_analytic (m : ℕ) :
    ∀ k w, AnalyticOnNhd ℝ (cartanIterateCoefficients K n m k w) Set.univ := by
  induction m with
  | zero =>
    intro k w
    exact analyticOnNhd_const
  | succ m ih =>
    intro k w
    exact analyticOnNhd_cartanCoefficientExtend K n _
      (analyticOnNhd_cartanSquareSumCoefficients K n (cartanIterateCoefficients K n m) ih) k.val w

/-- The concrete polynomial operator has real analytic coefficients everywhere. -/
theorem cartanPolynomialCoordinateOperator_analyticCoefficients (p : Polynomial ℂ) :
    (cartanPolynomialCoordinateOperator K n p).AnalyticCoefficientsOn Set.univ := by
  intro k w x hx
  change AnalyticAt ℝ
    (fun y => p.sum fun m c =>
      c * cartanCoefficientExtend K n (cartanIterateCoefficients K n m) k.val w y) x
  unfold Polynomial.sum
  apply Finset.analyticAt_fun_sum
  intro m _
  exact analyticAt_const.mul
    (analyticOnNhd_cartanCoefficientExtend K n (cartanIterateCoefficients K n m)
      (cartanIterateCoefficients_analytic K n m) k.val w x hx)

end Langlands.Global.ArchimedeanGL
