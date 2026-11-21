import Langlands.HarmonicAnalysis.Distribution.FullTestChartTransport
import Mathlib.Analysis.Complex.Basic

/-! # Linear changes of coordinates for complex smooth tests -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "Full(" X ")" => 𝓓((⊤ : Opens X), ℂ)

private def complexPullbackReal (A : E ≃L[ℝ] X) : Full(X) →L[ℝ] Full(E) :=
  let R := fullSmoothTestPullbackCLM A
  let ofImag := Complex.I • Complex.ofRealCLM
  (TestFunction.postcompCLM Complex.ofRealCLM).comp (R.comp (TestFunction.postcompCLM Complex.reCLM)) +
    (TestFunction.postcompCLM ofImag).comp (R.comp (TestFunction.postcompCLM Complex.imCLM))

private theorem complexPullbackReal_apply (A : E ≃L[ℝ] X) (φ : Full(X)) (y : E) :
    complexPullbackReal A φ y = φ (A y) := by
  simp only [complexPullbackReal, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    TestFunction.postcompCLM_apply, Function.comp_apply, fullSmoothTestPullbackCLM_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im _

/-- Pullback of complex smooth tests on full real normed spaces along a continuous
linear equivalence of the spaces. -/
def fullComplexSmoothTestPullbackCLM (A : E ≃L[ℝ] X) : Full(X) →L[ℂ] Full(E) :=
  ⟨{ toFun := complexPullbackReal A
     map_add' := map_add (complexPullbackReal A)
     map_smul' c f := by
       ext y
       simp only [complexPullbackReal_apply, smul_apply, RingHom.id_apply] },
    (complexPullbackReal A).continuous⟩

@[simp] theorem fullComplexSmoothTestPullbackCLM_apply (A : E ≃L[ℝ] X) (φ : Full(X)) (y : E) :
    fullComplexSmoothTestPullbackCLM A φ y = φ (A y) := complexPullbackReal_apply A φ y

theorem tsupport_fullComplexSmoothTestPullbackCLM_subset (A : E ≃L[ℝ] X) (φ : Full(X)) :
    tsupport (fullComplexSmoothTestPullbackCLM A φ) ⊆ A ⁻¹' tsupport φ := by
  apply closure_minimal _ ((isClosed_tsupport φ).preimage A.continuous)
  intro y hy
  by_contra h
  exact hy ((fullComplexSmoothTestPullbackCLM_apply A φ y).trans (image_eq_zero_of_notMem_tsupport h))

/-- A full-space change of real linear coordinates acts continuously and complex-linearly
on complex tests and pulls their support back to the corresponding closed set. -/
def ComplexSmoothTestTransportStatement : Prop :=
  ∀ {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : E ≃L[ℝ] X), ∃ P : Full(X) →L[ℂ] Full(E),
      (∀ (φ : Full(X)) (y : E), P φ y = φ (A y)) ∧ ∀ φ, tsupport (P φ) ⊆ A ⁻¹' tsupport φ

theorem complexSmoothTestTransport : ComplexSmoothTestTransportStatement :=
  fun A => ⟨fullComplexSmoothTestPullbackCLM A, fullComplexSmoothTestPullbackCLM_apply A,
    tsupport_fullComplexSmoothTestPullbackCLM_subset A⟩

end Langlands.HarmonicAnalysis
