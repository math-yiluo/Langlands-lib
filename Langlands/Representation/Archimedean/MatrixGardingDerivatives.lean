import Langlands.Representation.Archimedean.MatrixTestFunctions
import Langlands.Representation.Archimedean.GardingRiesz

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Set
open scoped Manifold ContDiff Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Langlands.GeneralLinear n F
local notation "Test" => 𝓓(matrixUnitsOpen F n, ℂ)

/-- A derivative of a left-translated test kernel changes the sign of the left field. -/
theorem gardingKernelDerivative_restrict (X : M) (f : Test) :
    gardingKernelDerivative X (matrixTestFunctionKernelEquiv f : G → ℂ) =
      (matrixTestFunctionKernelEquiv (-matrixLeftTestDerivative X f) : G → ℂ) := by
  funext y
  let k : M → M := fun x => Ring.inverse x * y.val
  have hk := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : G)).mul_const' y.val
  change HasFDerivAt k _ (1 : M) at hk
  have hk1 : k 1 = y.val := by simp [k, Ring.inverse_one]
  have hf := f.contDiff.differentiable (by simp) (k 1)
  have hc := hf.hasFDerivAt.comp (1 : M) hk
  have hφ (g : G) :
      (matrixTestFunctionKernelEquiv f : G → ℂ) (g⁻¹ * y) = ((f : M → ℂ) ∘ k) g.val := by
    simp [k]
  unfold gardingKernelDerivative
  rw [mfderiv_eq_fderiv_of_eq_comp hφ (1 : G) hc.differentiableAt]
  change (fderiv ℝ ((f : M → ℂ) ∘ k) (1 : M)) X = -matrixLeftTestDerivative X f y.val
  rw [hc.fderiv]
  simp [hk1, ContinuousLinearMap.mulLeftRight_apply]

/-- Differentiating an adjoint kernel on the left differentiates the original
test function along the right field before taking its adjoint. -/
theorem gardingKernelDerivative_adjoint_restrict (X : M) (f : Test) :
    gardingKernelDerivative X (adjointGardingKernel (matrixTestFunctionKernelEquiv f) : G → ℂ) =
      (adjointGardingKernel
        (matrixTestFunctionKernelEquiv (matrixRightTestDerivative X f)) : G → ℂ) := by
  funext y
  let k : M → M := fun x => y⁻¹.val * x
  have hk := (hasFDerivAt_id (𝕜 := ℝ) (1 : M)).const_mul y⁻¹.val
  change HasFDerivAt k _ (1 : M) at hk
  have hk1 : k 1 = y⁻¹.val := mul_one _
  let c : ℂ →L[ℝ] ℂ := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ)
  have hf := f.contDiff.differentiable (by simp) (k 1)
  have hc := c.hasFDerivAt.comp (1 : M) (hf.hasFDerivAt.comp (1 : M) hk)
  have hφ (g : G) : (adjointGardingKernel (matrixTestFunctionKernelEquiv f) : G → ℂ)
      (g⁻¹ * y) = (c ∘ (f : M → ℂ) ∘ k) g.val := by
    change star (f ((g⁻¹ * y)⁻¹ : G).val) = star (f (y⁻¹.val * g.val))
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
  unfold gardingKernelDerivative
  rw [mfderiv_eq_fderiv_of_eq_comp hφ (1 : G) hc.differentiableAt]
  change (fderiv ℝ (c ∘ (f : M → ℂ) ∘ k) (1 : M)) X =
    c (matrixRightTestDerivative X f y⁻¹.val)
  rw [hc.fderiv]
  change c (fderiv ℝ (f : M → ℂ) (k 1) (y⁻¹.val * X)) =
    c (matrixRightTestDerivative X f y⁻¹.val)
  rw [hk1, matrixRightTestDerivative_apply]

/-- The test-function operator for a word of derivatives of a left-translated kernel. -/
def matrixGardingTestWord : List M → Test →L[ℂ] Test
  | [] => ContinuousLinearMap.id ℂ Test
  | X :: Xs => (-matrixLeftTestDerivative X).comp (matrixGardingTestWord Xs)

/-- The successive derivatives of a test function along the right multiplication fields. -/
def matrixRightTestWord : List M → Test →L[ℂ] Test
  | [] => ContinuousLinearMap.id ℂ Test
  | X :: Xs => (matrixRightTestDerivative X).comp (matrixRightTestWord Xs)

theorem gardingKernelWord_restrict (Xs : List M) (f : Test) :
    gardingKernelWord Xs (matrixTestFunctionKernelEquiv f : G → ℂ) =
      (matrixTestFunctionKernelEquiv (matrixGardingTestWord Xs f) : G → ℂ) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      rw [gardingKernelWord, ih, gardingKernelDerivative_restrict]
      rfl

theorem gardingKernelWord_adjoint_restrict (Xs : List M) (f : Test) :
    gardingKernelWord Xs (adjointGardingKernel (matrixTestFunctionKernelEquiv f) : G → ℂ) =
      (adjointGardingKernel
        (matrixTestFunctionKernelEquiv (matrixRightTestWord Xs f)) : G → ℂ) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      rw [gardingKernelWord, ih, gardingKernelDerivative_adjoint_restrict]
      rfl

theorem tsupport_matrixGardingTestWord_subset (Xs : List M) (f : Test) :
    tsupport (matrixGardingTestWord Xs f : M → ℂ) ⊆ tsupport f := by
  induction Xs with
  | nil => exact Subset.rfl
  | cons X Xs ih =>
      change tsupport (-(matrixLeftTestDerivative X (matrixGardingTestWord Xs f) : M → ℂ)) ⊆ _
      rw [tsupport_neg]
      exact (tsupport_matrixLeftTestDerivative_subset X _).trans ih

theorem tsupport_matrixRightTestWord_subset (Xs : List M) (f : Test) :
    tsupport (matrixRightTestWord Xs f : M → ℂ) ⊆ tsupport f := by
  induction Xs with
  | nil => exact Subset.rfl
  | cons X Xs ih =>
      exact (tsupport_matrixRightTestDerivative_subset X _).trans ih

end Langlands.Archimedean
