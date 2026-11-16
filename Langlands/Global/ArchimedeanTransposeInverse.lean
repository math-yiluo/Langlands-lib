import Langlands.Global.ArchimedeanLieAlgebra

/-! # Negative transpose on the actual archimedean Lie and enveloping algebras -/

noncomputable section
universe u
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] (n : ℕ)

/-- The differential of transpose inverse is negative transpose. -/
def realLieIota : RealLieAlgebra F n ≃ₗ⁅ℝ⁆ RealLieAlgebra F n :=
  { toFun := fun X => (realLieAlgebraToMatrix F n).symm (-(realLieAlgebraToMatrix F n X).transpose)
    invFun := fun X => (realLieAlgebraToMatrix F n).symm (-(realLieAlgebraToMatrix F n X).transpose)
    left_inv := by
      intro X
      apply (realLieAlgebraToMatrix F n).injective
      simp
    right_inv := by
      intro X
      apply (realLieAlgebraToMatrix F n).injective
      simp
    map_add' := by
      intro X Y
      apply (realLieAlgebraToMatrix F n).injective
      simp [add_comm]
    map_smul' := by
      intro c X
      apply (realLieAlgebraToMatrix F n).injective
      simp [Matrix.transpose_smul]
    map_lie' := by
      intro X Y
      apply (realLieAlgebraToMatrix F n).injective
      simp only [LinearEquiv.apply_symm_apply, realLieAlgebraToMatrix_lie,
        Matrix.transpose_sub, Matrix.transpose_mul, neg_sub, neg_mul_neg] }

@[simp]
theorem realLieIota_matrix (X : RealLieAlgebra F n) :
    realLieAlgebraToMatrix F n (realLieIota F n X) = -(realLieAlgebraToMatrix F n X).transpose := rfl

@[simp]
theorem realLieIota_involutive (X : RealLieAlgebra F n) : realLieIota F n (realLieIota F n X) = X := by
  apply (realLieAlgebraToMatrix F n).injective
  simp

/-- Complexification of the differential of transpose inverse. -/
def complexLieIota : ComplexLieAlgebra F n ≃ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  { (realLieIota F n).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realLieIota F n).toLieHom).map_lie X Y }

@[simp]
theorem complexLieIota_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    complexLieIota F n (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] realLieIota F n X := rfl

@[simp]
theorem complexLieIota_involutive (X : ComplexLieAlgebra F n) :
    complexLieIota F n (complexLieIota F n X) = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

attribute [local instance 100] LieRing.ofAssociativeRing

private def envelopingIotaHom : EnvelopingAlgebra F n →ₐ[ℂ] EnvelopingAlgebra F n :=
  UniversalEnvelopingAlgebra.lift ℂ ((envelopingGenerator F n).comp (complexLieIota F n).toLieHom)

private theorem envelopingIotaHom_generator (X : ComplexLieAlgebra F n) :
    envelopingIotaHom F n (envelopingGenerator F n X) =
      envelopingGenerator F n (complexLieIota F n X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

private theorem envelopingIotaHom_involutive :
    (envelopingIotaHom F n).comp (envelopingIotaHom F n) = AlgHom.id ℂ _ := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingIotaHom F n (envelopingIotaHom F n (envelopingGenerator F n X)) =
    envelopingGenerator F n X
  rw [envelopingIotaHom_generator, envelopingIotaHom_generator, complexLieIota_involutive]

/-- The involution induced by transpose inverse on the actual enveloping algebra. -/
def envelopingIota : EnvelopingAlgebra F n ≃ₐ[ℂ] EnvelopingAlgebra F n :=
  { envelopingIotaHom F n with
    invFun := envelopingIotaHom F n
    left_inv := fun a => AlgHom.congr_fun (envelopingIotaHom_involutive F n) a
    right_inv := fun a => AlgHom.congr_fun (envelopingIotaHom_involutive F n) a }

@[simp]
theorem envelopingIota_generator (X : ComplexLieAlgebra F n) :
    envelopingIota F n (envelopingGenerator F n X) =
      envelopingGenerator F n (complexLieIota F n X) := envelopingIotaHom_generator F n X

@[simp]
theorem envelopingIota_involutive (a : EnvelopingAlgebra F n) :
    envelopingIota F n (envelopingIota F n a) = a :=
  AlgHom.congr_fun (envelopingIotaHom_involutive F n) a

/-- Restriction to the genuine algebra center. -/
def centerIota : EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n where
  toFun z := ⟨envelopingIota F n z.val,
    Subalgebra.map_center_le_center (envelopingIota F n).surjective ⟨z.val, z.property, rfl⟩⟩
  invFun z := ⟨envelopingIota F n z.val,
    Subalgebra.map_center_le_center (envelopingIota F n).surjective ⟨z.val, z.property, rfl⟩⟩
  left_inv z := Subtype.ext (envelopingIota_involutive F n z.val)
  right_inv z := Subtype.ext (envelopingIota_involutive F n z.val)
  map_mul' z w := Subtype.ext (map_mul (envelopingIota F n) z.val w.val)
  map_add' z w := Subtype.ext (map_add (envelopingIota F n) z.val w.val)
  commutes' c := Subtype.ext ((envelopingIota F n).commutes c)

@[simp]
theorem centerInclusion_centerIota (z : EnvelopingCenter F n) :
    centerInclusion F n (centerIota F n z) = envelopingIota F n (centerInclusion F n z) := rfl

@[simp]
theorem centerIota_involutive (z : EnvelopingCenter F n) :
    centerIota F n (centerIota F n z) = z := Subtype.ext (envelopingIota_involutive F n z.val)

end Langlands.Global.ArchimedeanGL
