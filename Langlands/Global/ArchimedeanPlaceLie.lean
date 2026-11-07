import Langlands.Global.ArchimedeanLieAlgebra
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Flat.Basic

/-! # Per-place factors of the actual archimedean Lie algebra -/

noncomputable section

universe u v

open scoped Classical TensorProduct
open NumberField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- Actual real-place scalar evaluation in the existing mixed coordinates. -/
def realPlaceScalarProjection (v : RP) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ where
  toFun x := x.1 v
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Actual complex-place scalar evaluation, considered as a real algebra map. -/
def complexPlaceScalarProjection (v : CP) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℂ where
  toFun x := x.2 v
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Projection of the actual real Lie algebra to one real matrix factor. -/
def realPlaceLieProjection (v : RP) : RealLieAlgebra F n →ₗ⁅ℝ⁆ RM :=
  { ((realPlaceScalarProjection F v).mapMatrix).toLinearMap.comp
      (realLieAlgebraToMatrix F n).toLinearMap with
    map_lie' := by
      intro X Y
      change (realPlaceScalarProjection F v).mapMatrix
        (realLieAlgebraToMatrix F n ⁅X, Y⁆) = _
      rw [realLieAlgebraToMatrix_lie, map_sub, map_mul, map_mul]
      rfl }

/-- Projection to a complex matrix factor retains its full underlying real Lie algebra. -/
def complexPlaceLieProjection (v : CP) : RealLieAlgebra F n →ₗ⁅ℝ⁆ CM :=
  { ((complexPlaceScalarProjection F v).mapMatrix).toLinearMap.comp
      (realLieAlgebraToMatrix F n).toLinearMap with
    map_lie' := by
      intro X Y
      change (complexPlaceScalarProjection F v).mapMatrix
        (realLieAlgebraToMatrix F n ⁅X, Y⁆) = _
      rw [realLieAlgebraToMatrix_lie, map_sub, map_mul, map_mul]
      rfl }

/-- The genuine global real Lie algebra is exactly the product of its local matrix factors. -/
def realLiePlaceCoordinates :
    RealLieAlgebra F n ≃ₗ⁅ℝ⁆ ((RP → RM) × (CP → CM)) where
  toFun X := (fun v => realPlaceLieProjection F n v X,
    fun v => complexPlaceLieProjection F n v X)
  invFun X := fun i j => (fun v => X.1 v i j, fun v => X.2 v i j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by
    intro X Y
    exact Prod.ext
      (funext fun v => (realPlaceLieProjection F n v).map_lie X Y)
      (funext fun v => (complexPlaceLieProjection F n v).map_lie X Y)

private def singleLieHom {I : Type u} (A : Type v) [Ring A] [Algebra ℝ A] (i : I) :
    A →ₗ⁅ℝ⁆ (I → A) :=
  { LinearMap.single ℝ (fun _ : I => A) i with
    map_lie' := by
      intro X Y
      funext j
      by_cases h : j = i
      · subst j
        simp
      · simp [h] }

/-- Insert a real-place matrix, with zero in all other real and complex factors. -/
def realPlaceLieInclusion (v : RP) : RM →ₗ⁅ℝ⁆ RealLieAlgebra F n :=
  (realLiePlaceCoordinates F n).symm.toLieHom.comp
    ((LieHom.inl ℝ (RP → RM) (CP → CM)).comp (singleLieHom RM v))

/-- Insert a complex-place matrix as a real direction, with zero at every other place. -/
def complexPlaceLieInclusion (v : CP) : CM →ₗ⁅ℝ⁆ RealLieAlgebra F n :=
  (realLiePlaceCoordinates F n).symm.toLieHom.comp
    ((LieHom.inr ℝ (RP → RM) (CP → CM)).comp (singleLieHom CM v))

@[simp] theorem realLiePlaceCoordinates_realInclusion (v : RP) (X : RM) :
    realLiePlaceCoordinates F n (realPlaceLieInclusion F n v X) =
      (Pi.single v X, 0) := by
  change realLiePlaceCoordinates F n ((realLiePlaceCoordinates F n).symm _) = _
  rw [LieEquiv.apply_symm_apply]
  apply Prod.ext
  · funext w
    by_cases h : w = v <;> simp [singleLieHom, h]
  · rfl

@[simp] theorem realLiePlaceCoordinates_complexInclusion (v : CP) (X : CM) :
    realLiePlaceCoordinates F n (complexPlaceLieInclusion F n v X) =
      (0, Pi.single v X) := by
  change realLiePlaceCoordinates F n ((realLiePlaceCoordinates F n).symm _) = _
  rw [LieEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext w
    by_cases h : w = v <;> simp [singleLieHom, h]

@[simp] theorem realProjection_realInclusion (v w : RP) (X : RM) :
    realPlaceLieProjection F n v (realPlaceLieInclusion F n w X) =
      (Pi.single w X : RP → RM) v :=
  congrArg (fun p : (RP → RM) × (CP → CM) => p.1 v)
    (realLiePlaceCoordinates_realInclusion F n w X)

@[simp] theorem complexProjection_complexInclusion (v w : CP) (X : CM) :
    complexPlaceLieProjection F n v (complexPlaceLieInclusion F n w X) =
      (Pi.single w X : CP → CM) v :=
  congrArg (fun p : (RP → RM) × (CP → CM) => p.2 v)
    (realLiePlaceCoordinates_complexInclusion F n w X)

@[simp] theorem realProjection_complexInclusion (v : RP) (w : CP) (X : CM) :
    realPlaceLieProjection F n v (complexPlaceLieInclusion F n w X) = 0 := rfl

@[simp] theorem complexProjection_realInclusion (v : CP) (w : RP) (X : RM) :
    complexPlaceLieProjection F n v (realPlaceLieInclusion F n w X) = 0 := rfl

theorem realPlaceLieInclusion_injective (v : RP) :
    Function.Injective (realPlaceLieInclusion F n v) := by
  intro X Y h
  simpa only [realProjection_realInclusion, Pi.single_eq_same] using
    congrArg (realPlaceLieProjection F n v) h

theorem complexPlaceLieInclusion_injective (v : CP) :
    Function.Injective (complexPlaceLieInclusion F n v) := by
  intro X Y h
  simpa only [complexProjection_complexInclusion, Pi.single_eq_same] using
    congrArg (complexPlaceLieProjection F n v) h

/-- Scalar extension of the real-place inclusion into the genuine global complex Lie algebra. -/
def realPlaceComplexLieInclusion (v : RP) :
    (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  { (realPlaceLieInclusion F n v).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realPlaceLieInclusion F n v)).map_lie X Y }

/-- Complexify the entire real Lie algebra of a complex place, retaining both real directions. -/
def complexPlaceComplexLieInclusion (v : CP) :
    (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  { (complexPlaceLieInclusion F n v).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (complexPlaceLieInclusion F n v)).map_lie X Y }

@[simp] theorem realPlaceComplexLieInclusion_tmul (v : RP) (z : ℂ) (X : RM) :
    realPlaceComplexLieInclusion F n v (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] realPlaceLieInclusion F n v X := rfl

@[simp] theorem complexPlaceComplexLieInclusion_tmul (v : CP) (z : ℂ) (X : CM) :
    complexPlaceComplexLieInclusion F n v (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] complexPlaceLieInclusion F n v X := rfl

theorem realPlaceComplexLieInclusion_injective (v : RP) :
    Function.Injective (realPlaceComplexLieInclusion F n v) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (realPlaceLieInclusion F n v).toLinearMap (realPlaceLieInclusion_injective F n v)

theorem complexPlaceComplexLieInclusion_injective (v : CP) :
    Function.Injective (complexPlaceComplexLieInclusion F n v) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (complexPlaceLieInclusion F n v).toLinearMap (complexPlaceLieInclusion_injective F n v)

variable [NumberField F]

/-- Every genuine real direction is the sum of its actual place-supported directions. -/
theorem sum_placeLieInclusions (X : RealLieAlgebra F n) :
    (∑ v : RP, realPlaceLieInclusion F n v (realPlaceLieProjection F n v X)) +
      (∑ v : CP, complexPlaceLieInclusion F n v (complexPlaceLieProjection F n v X)) = X := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext v
    change realPlaceLieProjection F n v _ = realPlaceLieProjection F n v X
    simp [map_add, map_sum]
  · funext v
    change complexPlaceLieProjection F n v _ = complexPlaceLieProjection F n v X
    simp [map_add, map_sum]

end Langlands.Global.ArchimedeanGL
