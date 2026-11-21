import Langlands.Global.ArchimedeanPlaceLie
import Langlands.Representation.Archimedean.Kostant.RealTransfer
import Langlands.Representation.Archimedean.DiagonalEnvelopingFactors
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Complex matrix factors of the actual archimedean Lie algebra -/

noncomputable section

universe u

open scoped Classical TensorProduct
open NumberField Langlands.Algebra Langlands.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- A real place gives one complex Lie factor and a complex place gives two. -/
abbrev ComplexLieMatrixPlace := RP ⊕ (CP × Fin 2)

private def flattenComplexPlaceMatrices :
    ((RP → CM) × (CP → Fin 2 → CM)) ≃ₗ[ℂ] (ComplexLieMatrixPlace F → CM) where
  toFun X := Sum.elim X.1 (fun p => X.2 p.1 p.2)
  invFun X := (fun v => X (.inl v), fun v a => X (.inr (v, a)))
  left_inv _ := rfl
  right_inv X := by funext p; cases p <;> rfl
  map_add' X Y := by funext p; cases p <;> rfl
  map_smul' c X := by funext p; cases p <;> rfl

private def realTensorMatrixEquiv : (ℂ ⊗[ℝ] RM) ≃ₗ⁅ℂ⁆ CM :=
  (Kostant.toGL n).trans (Kostant.unitMatrixLieEquiv n)

private theorem realTensorMatrixEquiv_tmul (z : ℂ) (X : RM) :
    realTensorMatrixEquiv n (z ⊗ₜ[ℝ] X) = z • X.map (algebraMap ℝ ℂ) :=
  Kostant.toGL_tmul n z X ()

private def realMatrixFactor (v : RP) : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ CM :=
  (realTensorMatrixEquiv n).toLieHom.comp
    { (realPlaceLieProjection F n v).toLinearMap.baseChange ℂ with
      map_lie' := fun {_ _} => (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realPlaceLieProjection F n v)).map_lie _ _ }

private def complexMatrixFactor (v : CP) : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ (Fin 2 → CM) :=
  (ComplexGenericLarge.tensorLieEquiv (n := n)).toLieHom.comp
    { (complexPlaceLieProjection F n v).toLinearMap.baseChange ℂ with
      map_lie' := fun {_ _} => (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (complexPlaceLieProjection F n v)).map_lie _ _ }

variable [NumberField F]

private def complexLieMatrixLinearEquiv : ComplexLieAlgebra F n ≃ₗ[ℂ] (ComplexLieMatrixPlace F → CM) :=
  let r := (TensorProduct.piRight ℝ ℂ ℂ (fun _ : RP => RM)).trans
    (LinearEquiv.piCongrRight fun _ => (realTensorMatrixEquiv n).toLinearEquiv)
  let c := (TensorProduct.piRight ℝ ℂ ℂ (fun _ : CP => CM)).trans
    (LinearEquiv.piCongrRight fun _ => (ComplexGenericLarge.tensorLieEquiv (n := n)).toLinearEquiv)
  (LieEnvelopingEquiv.complex (realLiePlaceCoordinates F n)).toLinearEquiv.trans
    ((TensorProduct.prodRight ℝ ℂ ℂ (RP → RM) (CP → CM)).trans
      ((r.prodCongr c).trans (flattenComplexPlaceMatrices F n)))

private theorem complexLieMatrixLinearEquiv_real (v : RP) (Y : ComplexLieAlgebra F n) :
    complexLieMatrixLinearEquiv F n Y (.inl v) = realMatrixFactor F n v Y := by
  induction Y using TensorProduct.inductionOn with
  | add X Y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z X =>
    change (realTensorMatrixEquiv n) ((TensorProduct.piRight ℝ ℂ ℂ (fun _ : RP => RM))
      (TensorProduct.prodRight ℝ ℂ ℂ (RP → RM) (CP → CM)
        ((LieEnvelopingEquiv.complex (realLiePlaceCoordinates F n)) (z ⊗ₜ[ℝ] X))).1 v) = _
    rw [LieEnvelopingEquiv.complex_tmul, TensorProduct.prodRight_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]
    rfl

private theorem complexLieMatrixLinearEquiv_complex (v : CP) (a : Fin 2) (Y : ComplexLieAlgebra F n) :
    complexLieMatrixLinearEquiv F n Y (.inr (v, a)) = complexMatrixFactor F n v Y a := by
  induction Y using TensorProduct.inductionOn with
  | add X Y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z X =>
    change (ComplexGenericLarge.tensorLieEquiv (n := n))
      ((TensorProduct.piRight ℝ ℂ ℂ (fun _ : CP => CM))
      (TensorProduct.prodRight ℝ ℂ ℂ (RP → RM) (CP → CM)
        ((LieEnvelopingEquiv.complex (realLiePlaceCoordinates F n)) (z ⊗ₜ[ℝ] X))).2 v) a = _
    rw [LieEnvelopingEquiv.complex_tmul, TensorProduct.prodRight_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]
    rfl

/-- The complex Lie algebra actually used for right differentiation, in its complex matrix factors. -/
def complexLieProductMatrixCoordinates :
    ComplexLieAlgebra F n ≃ₗ⁅ℂ⁆ Kostant.GLProd ℂ (fun _ : ComplexLieMatrixPlace F => n) where
  __ := complexLieMatrixLinearEquiv F n
  map_lie' := fun {X Y} => by
    funext p
    cases p with
    | inl v =>
      change complexLieMatrixLinearEquiv F n ⁅X, Y⁆ (.inl v) =
        ⁅complexLieMatrixLinearEquiv F n X (.inl v), complexLieMatrixLinearEquiv F n Y (.inl v)⁆
      simp only [complexLieMatrixLinearEquiv_real, LieHom.map_lie]
    | inr p =>
      obtain ⟨v, a⟩ := p
      change complexLieMatrixLinearEquiv F n ⁅X, Y⁆ (.inr (v, a)) =
        ⁅complexLieMatrixLinearEquiv F n X (.inr (v, a)), complexLieMatrixLinearEquiv F n Y (.inr (v, a))⁆
      simp only [complexLieMatrixLinearEquiv_complex]
      exact congrFun ((complexMatrixFactor F n v).map_lie X Y) a

@[simp]
theorem complexLieProductMatrixCoordinates_tmul_real (z : ℂ) (X : RealLieAlgebra F n) (v : RP) :
    complexLieProductMatrixCoordinates F n (z ⊗ₜ[ℝ] X) (.inl v) =
      z • (realPlaceLieProjection F n v X).map (algebraMap ℝ ℂ) := by
  change complexLieMatrixLinearEquiv F n _ _ = _
  rw [complexLieMatrixLinearEquiv_real]
  exact realTensorMatrixEquiv_tmul n z _

@[simp]
theorem complexLieProductMatrixCoordinates_tmul_complex (z : ℂ) (X : RealLieAlgebra F n) (v : CP) (a : Fin 2) :
    complexLieProductMatrixCoordinates F n (z ⊗ₜ[ℝ] X) (.inr (v, a)) =
      z • ComplexGenericLarge.pairHom (complexPlaceLieProjection F n v X) a := by
  change complexLieMatrixLinearEquiv F n _ _ = _
  rw [complexLieMatrixLinearEquiv_complex]
  exact congrFun (ComplexGenericLarge.tensorEquiv_tmul z (complexPlaceLieProjection F n v X)) a

end Langlands.Global.ArchimedeanGL
