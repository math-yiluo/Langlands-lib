import Langlands.HarmonicAnalysis.Distribution.FullTestChartTransport
import Langlands.HarmonicAnalysis.Distribution.RealMatrixCutoff
import Langlands.Representation.Archimedean.RealReverseTwist

/-! # The transpose-odd part of a distribution on real matrices -/

noncomputable section

open scoped ContDiff Distributions Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}

local notation "Mat" n => Matrix (Fin n) (Fin n) ℝ
local notation "GL" n => Langlands.GeneralLinear n ℝ

/-- Matrix conjugation as a continuous real linear equivalence. -/
abbrev fullConjugationEquiv (g : GL n) : (Mat n) ≃L[ℝ] (Mat n) :=
  ((g.mulLeftLinearEquiv ℝ (Mat n)).trans ((g⁻¹).mulRightLinearEquiv ℝ)).toContinuousLinearEquiv

@[simp]
theorem fullConjugationEquiv_apply (g : GL n) (A : Mat n) :
    fullConjugationEquiv g A = (g : Mat n) * A * ((g⁻¹ : GL n) : Mat n) := rfl

/-- Matrix transpose as a continuous real linear equivalence. -/
abbrev fullTransposeEquiv (n : ℕ) : (Mat n) ≃L[ℝ] (Mat n) :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv

@[simp]
theorem fullTransposeEquiv_apply (A : Mat n) : fullTransposeEquiv n A = Aᵀ := rfl

@[simp]
theorem fullSmoothTestPullbackCLM_fullConjugation (g : GL n) (f : FullTest n) :
    fullSmoothTestPullbackCLM (fullConjugationEquiv g) f = fullConjugationTest g f := by
  ext A
  exact fullSmoothTestPullbackCLM_apply (fullConjugationEquiv g) f A

@[simp]
theorem fullSmoothTestPullbackCLM_fullTranspose (f : FullTest n) :
    fullSmoothTestPullbackCLM (fullTransposeEquiv n) f = fullTransposeTest f := by
  ext A
  exact fullSmoothTestPullbackCLM_apply (fullTransposeEquiv n) f A

open Archimedean.RealReverseTwist in
private theorem fullTransposeTest_fullConjugationTest (g : GL n) (f : FullTest n) :
    fullTransposeTest (fullConjugationTest g f) =
      fullConjugationTest (transposeGL g⁻¹) (fullTransposeTest f) := by
  ext A
  simp only [fullConjugationTest_apply, fullTransposeTest_apply, transposeGL_val,
    transposeGL_inv_val, inv_inv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

@[simp]
theorem fullTransposeTest_fullTransposeTest (f : FullTest n) :
    fullTransposeTest (fullTransposeTest f) = f := by
  ext A
  simp

/-- A distribution transforms by the sign of transposition if transposition
acts by negation on every test evaluation. -/
def IsFullTransposeAntiInvariant (D : FullDistribution n) : Prop :=
  ∀ f : FullTest n, D (fullTransposeTest f) = -D f

/-- The difference of a distribution and its transport by matrix transpose. -/
def transposeOddDistribution (D : FullDistribution n) : FullDistribution n :=
  let Dt : FullDistribution n := D.comp (fullSmoothTestPullbackCLM (fullTransposeEquiv n))
  D - Dt

@[simp]
theorem transposeOddDistribution_apply (D : FullDistribution n) (f : FullTest n) :
    transposeOddDistribution D f = D f - D (fullTransposeTest f) := by
  change D f - D (fullSmoothTestPullbackCLM (fullTransposeEquiv n) f) = _
  rw [fullSmoothTestPullbackCLM_fullTranspose]

theorem isFullConjugationInvariant_transposeOddDistribution (D : FullDistribution n)
    (hD : IsFullConjugationInvariant D) :
    IsFullConjugationInvariant (transposeOddDistribution D) := by
  intro g f
  rw [transposeOddDistribution_apply, transposeOddDistribution_apply, hD g f,
    fullTransposeTest_fullConjugationTest,
    hD (Archimedean.RealReverseTwist.transposeGL g⁻¹) (fullTransposeTest f)]

theorem isFullTransposeAntiInvariant_transposeOddDistribution (D : FullDistribution n) :
    IsFullTransposeAntiInvariant (transposeOddDistribution D) := by
  intro f
  rw [transposeOddDistribution_apply, transposeOddDistribution_apply,
    fullTransposeTest_fullTransposeTest]
  abel

theorem transposeOddDistribution_eq_zero_iff (D : FullDistribution n) :
    transposeOddDistribution D = 0 ↔ IsFullTransposeInvariant D := by
  constructor
  · intro h f
    have hf : transposeOddDistribution D f = 0 := by rw [h]; rfl
    rw [transposeOddDistribution_apply, sub_eq_zero] at hf
    exact hf.symm
  · intro h
    apply DFunLike.ext
    intro f
    rw [transposeOddDistribution_apply, h f, sub_self]
    rfl

/-- Vanishing of conjugation-invariant distributions with the transpose sign
implies transpose invariance of all conjugation-invariant distributions. -/
theorem isFullTransposeInvariant_of_antiInvariant_eq_zero
    (h : ∀ T : FullDistribution n, IsFullConjugationInvariant T →
      IsFullTransposeAntiInvariant T → T = 0)
    (D : FullDistribution n) (hD : IsFullConjugationInvariant D) :
    IsFullTransposeInvariant D :=
  (transposeOddDistribution_eq_zero_iff D).mp
    (h _ (isFullConjugationInvariant_transposeOddDistribution D hD)
      (isFullTransposeAntiInvariant_transposeOddDistribution D))

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
