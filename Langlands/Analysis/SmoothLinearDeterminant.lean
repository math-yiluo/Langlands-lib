import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

/-! # Differentiation of the real determinant at a linear isomorphism -/

noncomputable section

open Function
open scoped ContDiff

set_option autoImplicit false

namespace Langlands.Analysis

private def rowDeterminant (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := by
    change Continuous (fun A : ι → ι → ℝ => (Matrix.of A).det)
    simp_rw [Matrix.det_apply']
    exact continuous_finsetSum _ fun σ _ => continuous_const.mul
      (continuous_finsetProd _ fun i _ => (continuous_apply i).comp (continuous_apply (σ i)))

private theorem det_updateRow_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℝ) : ((1 : Matrix ι ι ℝ).updateRow i v).det = v i := by
  have hv : v = ∑ j, v j • (1 : Matrix ι ι ℝ) j := by
    ext k
    simp [Matrix.one_apply, Finset.sum_ite_eq']
  conv_lhs => rw [hv]
  rw [Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace of a continuous real endomorphism of a finite-dimensional space,
as a continuous linear functional. -/
def continuousEndomorphismTrace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →L[ℝ] E) →L[ℝ] ℝ :=
  (show (E →L[ℝ] E) →ₗ[ℝ] ℝ from
    { toFun := fun A => LinearMap.trace ℝ E A.toLinearMap
      map_add' := fun A B => map_add (LinearMap.trace ℝ E) A.toLinearMap B.toLinearMap
      map_smul' := fun a A => map_smul (LinearMap.trace ℝ E) a A.toLinearMap }).toContinuousLinearMap

@[simp]
theorem continuousEndomorphismTrace_apply (A : E →L[ℝ] E) :
    continuousEndomorphismTrace E A = LinearMap.trace ℝ E A.toLinearMap := rfl

private def endomorphismCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) : (E →L[ℝ] E) →L[ℝ] (ι → ι → ℝ) :=
  (show (E →L[ℝ] E) →ₗ[ℝ] (ι → ι → ℝ) from
    { toFun := fun A => LinearMap.toMatrix b b A.toLinearMap
      map_add' := fun A B => map_add (LinearMap.toMatrix b b) A.toLinearMap B.toLinearMap
      map_smul' := fun a A => map_smul (LinearMap.toMatrix b b) a A.toLinearMap }).toContinuousLinearMap

/-- The determinant is smooth on the space of continuous real endomorphisms. -/
theorem contDiff_continuousLinearMap_det :
    ContDiff ℝ ∞ (fun A : E →L[ℝ] E => A.det) := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let C := endomorphismCoordinates b
  have heq : (fun A : E →L[ℝ] E => A.det) = rowDeterminant _ ∘ C := by
    funext A
    exact (LinearMap.det_toMatrix b A.toLinearMap).symm
  rw [heq]
  have hd : ContDiff ℝ ∞ (rowDeterminant (Module.Free.ChooseBasisIndex ℝ E)) :=
    (rowDeterminant (Module.Free.ChooseBasisIndex ℝ E)).contDiff
  exact hd.comp C.contDiff

/-- The differential of the determinant at the identity is the trace. -/
theorem hasFDerivAt_continuousLinearMap_det_one :
    HasFDerivAt (fun A : E →L[ℝ] E => A.det) (continuousEndomorphismTrace E) 1 := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let C := endomorphismCoordinates b
  have hC (A : E →L[ℝ] E) : C A = LinearMap.toMatrix b b A.toLinearMap := rfl
  have hC1 : C (1 : E →L[ℝ] E) = (1 : Matrix _ _ ℝ) := by
    rw [hC]
    exact LinearMap.toMatrix_one b
  have heq : (fun A : E →L[ℝ] E => A.det) = rowDeterminant _ ∘ C := by
    funext A
    exact (LinearMap.det_toMatrix b A.toLinearMap).symm
  rw [heq]
  let D := rowDeterminant (Module.Free.ChooseBasisIndex ℝ E)
  refine ((D.hasFDerivAt (C 1)).comp (1 : E →L[ℝ] E) C.hasFDerivAt).congr_fderiv ?_
  ext A
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (Matrix.updateRow (Matrix.of (C 1)) i (C A i)).det) =
    LinearMap.trace ℝ E A.toLinearMap
  have h1 : Matrix.of (C 1) = (1 : Matrix _ _ ℝ) := hC1
  simp_rw [h1, det_updateRow_one, hC, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace,
    Matrix.diag_apply]

/-- Jacobi's formula for the differential of the determinant at an invertible
continuous linear map. -/
theorem hasFDerivAt_continuousLinearMap_det (L : E ≃L[ℝ] E) :
    HasFDerivAt (fun A : E →L[ℝ] E => A.det)
      (L.toContinuousLinearMap.det • ((continuousEndomorphismTrace E).comp
        (ContinuousLinearMap.compL ℝ E E E L.symm.toContinuousLinearMap)))
      L.toContinuousLinearMap := by
  let C := ContinuousLinearMap.compL ℝ E E E L.symm.toContinuousLinearMap
  have hC : C L.toContinuousLinearMap = 1 := by
    ext x
    exact L.symm_apply_apply x
  have hdet : HasFDerivAt (fun A : E →L[ℝ] E => A.det) (continuousEndomorphismTrace E)
      (C L.toContinuousLinearMap) := by
    rw [hC]
    exact hasFDerivAt_continuousLinearMap_det_one
  have hc := hdet.comp L.toContinuousLinearMap C.hasFDerivAt
  have heq : (fun A : E →L[ℝ] E => L.toContinuousLinearMap.det * (C A).det) =
      fun A : E →L[ℝ] E => A.det := by
    funext A
    change L.toLinearMap.det * (L.symm.toLinearMap.comp A.toLinearMap).det = A.det
    rw [← LinearMap.det_comp, ← LinearMap.comp_assoc]
    have hinv : L.toLinearMap.comp L.symm.toLinearMap = LinearMap.id := by
      ext x
      exact L.apply_symm_apply x
    rw [hinv, LinearMap.id_comp]
  rw [← heq]
  exact hc.const_smul L.toContinuousLinearMap.det

end Langlands.Analysis
