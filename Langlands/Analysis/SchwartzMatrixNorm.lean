import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Matrix.Normed

/-! # Transfer of Schwartz functions between the two complex matrix norms -/

noncomputable section

open scoped SchwartzMap

set_option autoImplicit false

namespace Langlands.Analysis.SchwartzMatrixNorm

open scoped Matrix.Norms.Operator in
/-- Complex matrix Schwartz functions with the supremum row-sum norm on the domain. -/
abbrev OperatorSchwartz (m n : ℕ) := 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ)

open scoped Matrix.Norms.Elementwise in
/-- Complex matrix Schwartz functions with the supremum entry norm on the domain. -/
abbrev EntrySchwartz (m n : ℕ) := 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ)

open scoped Matrix.Norms.Elementwise in
/-- The identity pullback from matrices with the operator norm to the same matrices with the
entrywise norm. -/
def operatorToEntry {m n : ℕ} (Φ : OperatorSchwartz m n) : EntrySchwartz m n :=
  @SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Matrix (Fin m) (Fin n) ℂ) (Matrix (Fin m) (Fin n) ℂ) ℂ
    Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _ _ _
    Matrix.normedAddCommGroup Matrix.normedSpace _
    (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m) (Fin n) ℂ)) Φ

@[simp]
theorem operatorToEntry_apply {m n : ℕ} (Φ : OperatorSchwartz m n) (X : Matrix (Fin m) (Fin n) ℂ) :
    operatorToEntry Φ X = Φ X := rfl

end Langlands.Analysis.SchwartzMatrixNorm
