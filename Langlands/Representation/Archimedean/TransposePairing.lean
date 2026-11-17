import Langlands.Representation.Archimedean.GKModule

/-! # The inverse-transpose pairing condition for an archimedean local module -/

noncomputable section
universe uV
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (𝕂 : Type) [RCLike 𝕂] (n : ℕ)

/-- Inverse transpose on the standard maximal compact subgroup of `GL_n(𝕂)`. -/
def compactIota : Matrix.unitaryGroup (Fin n) 𝕂 ≃* Matrix.unitaryGroup (Fin n) 𝕂 where
  toFun k := Matrix.UnitaryGroup.transpose k⁻¹
  invFun k := Matrix.UnitaryGroup.transpose k⁻¹
  left_inv k := by ext i j; simp [Matrix.UnitaryGroup.transpose]
  right_inv k := by ext i j; simp [Matrix.UnitaryGroup.transpose]
  map_mul' k l := by
    apply Subtype.ext
    simp [Matrix.UnitaryGroup.transpose, Matrix.transpose_mul]

@[simp]
theorem compactIota_coe (k : Matrix.unitaryGroup (Fin n) 𝕂) :
    (compactIota 𝕂 n k : Matrix (Fin n) (Fin n) 𝕂) =
      ((k⁻¹ : Matrix.unitaryGroup (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂).transpose := rfl

@[simp]
theorem compactIota_involutive (k : Matrix.unitaryGroup (Fin n) 𝕂) :
    compactIota 𝕂 n (compactIota 𝕂 n k) = k :=
  (compactIota 𝕂 n).left_inv k

/-- On a unitary matrix, inverse transpose is entrywise conjugation. -/
theorem compactIota_eq_map_star (k : Matrix.unitaryGroup (Fin n) 𝕂) :
    compactIota 𝕂 n k = Matrix.UnitaryGroup.map_star k := by
  ext i j
  rfl

/-- On the real orthogonal group, inverse transpose is the identity. -/
@[simp]
theorem compactIota_real (k : Matrix.unitaryGroup (Fin n) ℝ) :
    compactIota ℝ n k = k := by
  ext i j
  simp [compactIota, Matrix.UnitaryGroup.transpose]

/-- Negative ordinary transpose, as a real Lie algebra automorphism. -/
def matrixLieIota :
    Matrix (Fin n) (Fin n) 𝕂 ≃ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) 𝕂 where
  toFun X := -X.transpose
  invFun X := -X.transpose
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by simp [add_comm]
  map_smul' c X := by simp [Matrix.transpose_smul]
  map_lie' := by
    intro X Y
    change -(X * Y - Y * X).transpose =
      (-X.transpose) * (-Y.transpose) - (-Y.transpose) * (-X.transpose)
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, neg_sub, neg_mul_neg]

@[simp]
theorem matrixLieIota_apply (X : Matrix (Fin n) (Fin n) 𝕂) :
    matrixLieIota 𝕂 n X = -X.transpose := rfl

@[simp]
theorem matrixLieIota_involutive (X : Matrix (Fin n) (Fin n) 𝕂) :
    matrixLieIota 𝕂 n (matrixLieIota 𝕂 n X) = X :=
  (matrixLieIota 𝕂 n).left_inv X

/-- Complexification of the real differential of inverse transpose. -/
def complexifiedMatrixLieIota :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) ≃ₗ⁅ℂ⁆
      (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) :=
  { (matrixLieIota 𝕂 n).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (matrixLieIota 𝕂 n).toLieHom).map_lie X Y }

@[simp]
theorem complexifiedMatrixLieIota_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) 𝕂) :
    complexifiedMatrixLieIota 𝕂 n (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] (-X.transpose) := rfl

@[simp]
theorem complexifiedMatrixLieIota_involutive
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) :
    complexifiedMatrixLieIota 𝕂 n (complexifiedMatrixLieIota 𝕂 n X) = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- A bilinear form whose second variable carries the inverse-transpose twist of
the compact and genuine complexified real Lie actions. -/
def IsTransposeInvariantGKPairing (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  (∀ (k : Matrix.unitaryGroup (Fin n) 𝕂) (y x : V),
    B (ρ k y) (ρ (compactIota 𝕂 n k) x) = B y x) ∧
  ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) (y x : V),
    B (π X y) x + B y (π (complexifiedMatrixLieIota 𝕂 n X) x) = 0

/-- The local inverse-transpose pairing existence condition. This definition does
not assert that any module satisfies it. -/
def HasNonzeroTransposeGKPairing : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, IsTransposeInvariantGKPairing 𝕂 n ρ π B ∧ B ≠ 0

end Langlands.Archimedean
