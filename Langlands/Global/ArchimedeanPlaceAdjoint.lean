import Langlands.Global.ArchimedeanAdjoint
import Langlands.Global.ArchimedeanPlaceLie
import Langlands.Global.ArchimedeanPlaceCompact

/-! # Actual matrix adjoints on the archimedean place Lie factors -/

noncomputable section
universe u v

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

private def matrixUnitsRealConjugation (𝕜 : Type v) [RCLike 𝕜] (n : ℕ)
    (g : (Matrix (Fin n) (Fin n) 𝕜)ˣ) :
    Matrix (Fin n) (Fin n) 𝕜 ≃ₐ[ℝ] Matrix (Fin n) (Fin n) 𝕜 where
  toFun X := g.val * X * g⁻¹.val
  invFun X := g⁻¹.val * X * g.val
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]
  map_mul' X Y := by simp [mul_assoc]
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes, mul_assoc]
    simp

/-- Actual conjugation of the underlying real matrix Lie algebra by a unitary matrix. -/
def unitaryMatrixRealLieConjugation (𝕜 : Type v) [RCLike 𝕜] (n : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 ≃ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) 𝕜 :=
  { (matrixUnitsRealConjugation 𝕜 n (Unitary.toUnits k)).toLinearEquiv with
    map_lie' := by
      intro X Y
      change matrixUnitsRealConjugation 𝕜 n (Unitary.toUnits k) (X * Y - Y * X) = _
      rw [map_sub, map_mul, map_mul]
      rfl }

@[simp] theorem unitaryMatrixRealLieConjugation_apply
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k : Matrix.unitaryGroup (Fin n) 𝕜)
    (X : Matrix (Fin n) (Fin n) 𝕜) :
    unitaryMatrixRealLieConjugation 𝕜 n k X = k.val * X * k⁻¹.val := rfl

/-- Complexify the entire underlying real matrix adjoint, including both complex-place directions. -/
def unitaryMatrixComplexLieConjugation (𝕜 : Type v) [RCLike 𝕜] (n : ℕ)
    (k : Matrix.unitaryGroup (Fin n) 𝕜) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) ≃ₗ⁅ℂ⁆
      (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜) :=
  { (unitaryMatrixRealLieConjugation 𝕜 n k).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (unitaryMatrixRealLieConjugation 𝕜 n k).toLieHom).map_lie X Y }

@[simp] theorem unitaryMatrixComplexLieConjugation_tmul
    (𝕜 : Type v) [RCLike 𝕜] (n : ℕ) (k : Matrix.unitaryGroup (Fin n) 𝕜)
    (z : ℂ) (X : Matrix (Fin n) (Fin n) 𝕜) :
    unitaryMatrixComplexLieConjugation 𝕜 n k (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] unitaryMatrixRealLieConjugation 𝕜 n k X := rfl

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- Projection of the original global adjoint is ordinary matrix conjugation at a real place. -/
theorem realProjection_realLieConjugation (v : RP) (g : InfiniteAdelicGL F n)
    (X : RealLieAlgebra F n) :
    realPlaceLieProjection F n v (realLieConjugation F n g X) =
      realMatrix F n (archimedeanGLCoordinates F n g) v *
        realPlaceLieProjection F n v X *
        realMatrix F n (archimedeanGLCoordinates F n g⁻¹) v := by
  change (realPlaceScalarProjection F v).mapMatrix
    (realLieAlgebraToMatrix F n (realLieConjugation F n g X)) = _
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul]
  rfl

theorem complexProjection_realLieConjugation (v : CP) (g : InfiniteAdelicGL F n)
    (X : RealLieAlgebra F n) :
    complexPlaceLieProjection F n v (realLieConjugation F n g X) =
      complexMatrix F n (archimedeanGLCoordinates F n g) v *
        complexPlaceLieProjection F n v X *
        complexMatrix F n (archimedeanGLCoordinates F n g⁻¹) v := by
  change (complexPlaceScalarProjection F v).mapMatrix
    (realLieAlgebraToMatrix F n (realLieConjugation F n g X)) = _
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul]
  rfl

/-- Any full compact coordinate product preserves the real-place inserted Lie algebra. -/
theorem realLieConjugation_realInclusion (p : ArchimedeanCompactFactors F n)
    (v : RP) (X : RM) :
    realLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (realPlaceLieInclusion F n v X) =
      realPlaceLieInclusion F n v (unitaryMatrixRealLieConjugation ℝ n (p.1 v) X) := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext w
    change realPlaceLieProjection F n w _ = realPlaceLieProjection F n w _
    rw [realProjection_realLieConjugation, map_inv,
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL,
      realProjection_realInclusion, realProjection_realInclusion]
    change (p.1 w).val * (Pi.single v X : RP → RM) w * ((p.1 w)⁻¹).val = _
    by_cases h : w = v
    · subst w
      simp only [Pi.single_eq_same, unitaryMatrixRealLieConjugation_apply]
    · simp [h]
  · funext w
    change complexPlaceLieProjection F n w _ = complexPlaceLieProjection F n w _
    rw [complexProjection_realLieConjugation, complexProjection_realInclusion,
      complexProjection_realInclusion]
    simp

/-- The complex-place factor is preserved as its full underlying real matrix Lie algebra. -/
theorem realLieConjugation_complexInclusion (p : ArchimedeanCompactFactors F n)
    (v : CP) (X : CM) :
    realLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (complexPlaceLieInclusion F n v X) =
      complexPlaceLieInclusion F n v (unitaryMatrixRealLieConjugation ℂ n (p.2 v) X) := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext w
    change realPlaceLieProjection F n w _ = realPlaceLieProjection F n w _
    rw [realProjection_realLieConjugation, realProjection_complexInclusion,
      realProjection_complexInclusion]
    simp
  · funext w
    change complexPlaceLieProjection F n w _ = complexPlaceLieProjection F n w _
    rw [complexProjection_realLieConjugation, map_inv,
      ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL,
      complexProjection_complexInclusion, complexProjection_complexInclusion]
    change (p.2 w).val * (Pi.single v X : CP → CM) w * ((p.2 w)⁻¹).val = _
    by_cases h : w = v
    · subst w
      simp only [Pi.single_eq_same, unitaryMatrixRealLieConjugation_apply]
    · simp [h]

/-- Scalar extension retains the genuine real-place adjoint intertwining identity. -/
theorem complexLieConjugation_realInclusion (p : ArchimedeanCompactFactors F n)
    (v : RP) (X : ℂ ⊗[ℝ] RM) :
    complexLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (realPlaceComplexLieInclusion F n v X) =
      realPlaceComplexLieInclusion F n v
        (unitaryMatrixComplexLieConjugation ℝ n (p.1 v) X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [realPlaceComplexLieInclusion_tmul, complexLieConjugation_tmul,
      unitaryMatrixComplexLieConjugation_tmul, realLieConjugation_realInclusion]
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem complexLieConjugation_complexInclusion (p : ArchimedeanCompactFactors F n)
    (v : CP) (X : ℂ ⊗[ℝ] CM) :
    complexLieConjugation F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n p)
        (complexPlaceComplexLieInclusion F n v X) =
      complexPlaceComplexLieInclusion F n v
        (unitaryMatrixComplexLieConjugation ℂ n (p.2 v) X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexPlaceComplexLieInclusion_tmul, complexLieConjugation_tmul,
      unitaryMatrixComplexLieConjugation_tmul, realLieConjugation_complexInclusion]
  | add X Y hX hY => simp only [map_add, hX, hY]

end Langlands.Global.ArchimedeanGL
