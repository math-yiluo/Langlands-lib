import Langlands.Representation.Archimedean.SmoothCasselmanWallachBound
import Langlands.Representation.Archimedean.SmoothHilbertTransposePairingReduction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The word-seminorm bound on finite-dimensional algebraic carriers -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe uV uE₁ uE₂

open DerivativeSmoothVectors

/-- On a finite-dimensional algebraic carrier the empty-word norm alone controls the
underlying norm of any linear map into a genuine smooth carrier. -/
def RealSmoothCasselmanWallachFiniteDimensionalStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    (R₁ : Langlands.GeneralLinear n ℝ →* (E₁ →L[ℂ] E₁))
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    (R₂ : Langlands.GeneralLinear n ℝ →* (E₂ →L[ℂ] E₂))
    (e : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ n) R₁)
    (f : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ n) R₂),
    Function.Injective e → ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V,
      ‖derivativeCLM (matrixModel ℝ n) R₂ [] (f v)‖ ≤
        C * ‖derivativeCLM (matrixModel ℝ n) R₁ [] (e v)‖

/-- Use the norm on the image of the source empty-word map and take the operator norm
of the descended linear map. -/
theorem realSmoothCasselmanWallachFiniteDimensional :
    RealSmoothCasselmanWallachFiniteDimensionalStatement.{uV, uE₁, uE₂} := by
  intro n V _ _ _ E₁ _ _ R₁ E₂ _ _ R₂ e f he
  let I := matrixModel ℝ n
  let a := (derivativeCLM I R₁ []).toLinearMap.comp e
  let b := (derivativeCLM I R₂ []).toLinearMap.comp f
  have ha : Function.Injective a := (derivativeCLM_nil_injective ℝ n R₁).comp he
  let ea := LinearEquiv.ofInjective a ha
  let : FiniteDimensional ℂ a.range := ea.finiteDimensional
  let T := (b.comp ea.symm.toLinearMap).toContinuousLinearMap
  refine ⟨‖T‖, T.opNorm_nonneg, fun v => ?_⟩
  have h := T.le_opNorm (ea v)
  change ‖b (ea.symm (ea v))‖ ≤ ‖T‖ * ‖a v‖ at h
  rw [ea.symm_apply_apply] at h
  exact h

end Langlands.Archimedean
