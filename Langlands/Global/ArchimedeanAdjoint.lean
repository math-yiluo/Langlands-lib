import Langlands.Global.ArchimedeanLieAlgebra
import Langlands.Global.AdelicGL

/-! # Actual archimedean adjoint automorphisms -/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

private def matrixConjugation (g : InfiniteAdelicGL K n) :
    ArchimedeanMatrix K n ≃ₐ[ℝ] ArchimedeanMatrix K n where
  toFun X := (archimedeanGLCoordinates K n g).val * X *
    (archimedeanGLCoordinates K n g)⁻¹.val
  invFun X := (archimedeanGLCoordinates K n g)⁻¹.val * X *
    (archimedeanGLCoordinates K n g).val
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]
  map_mul' X Y := by simp [mul_assoc]
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes, mul_assoc]
    simp

/-- Actual matrix conjugation, with convention `Ad(g) X = g X g⁻¹`. -/
def realLieConjugation (g : InfiniteAdelicGL K n) :
    RealLieAlgebra K n ≃ₗ⁅ℝ⁆ RealLieAlgebra K n :=
  { ((realLieAlgebraToMatrix K n).trans (matrixConjugation K n g).toLinearEquiv).trans
      (realLieAlgebraToMatrix K n).symm with
    map_lie' := by
      intro X Y
      apply (realLieAlgebraToMatrix K n).injective
      change matrixConjugation K n g
        (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y -
          realLieAlgebraToMatrix K n Y * realLieAlgebraToMatrix K n X) =
        matrixConjugation K n g (realLieAlgebraToMatrix K n X) *
          matrixConjugation K n g (realLieAlgebraToMatrix K n Y) -
        matrixConjugation K n g (realLieAlgebraToMatrix K n Y) *
          matrixConjugation K n g (realLieAlgebraToMatrix K n X)
      rw [map_sub, map_mul, map_mul] }

theorem realLieConjugation_apply (g : InfiniteAdelicGL K n) (X : RealLieAlgebra K n) :
    realLieConjugation K n g X = (realLieAlgebraToMatrix K n).symm
      ((archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n X *
        (archimedeanGLCoordinates K n g⁻¹).val) := by
  simp only [realLieConjugation, matrixConjugation, map_inv]
  rfl

@[simp]
theorem realLieAlgebraToMatrix_realLieConjugation (g : InfiniteAdelicGL K n)
    (X : RealLieAlgebra K n) :
    realLieAlgebraToMatrix K n (realLieConjugation K n g X) =
      (archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n X *
        (archimedeanGLCoordinates K n g⁻¹).val := by
  rw [realLieConjugation_apply, LinearEquiv.apply_symm_apply]

@[simp]
theorem realLieConjugation_one :
    realLieConjugation K n 1 = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  apply (realLieAlgebraToMatrix K n).injective
  simp

theorem realLieConjugation_mul (g h : InfiniteAdelicGL K n) :
    realLieConjugation K n (g * h) =
      (realLieConjugation K n h).trans (realLieConjugation K n g) := by
  apply LieEquiv.ext
  intro X
  apply (realLieAlgebraToMatrix K n).injective
  simp [mul_assoc]

@[simp]
theorem realLieConjugation_inv (g : InfiniteAdelicGL K n) :
    realLieConjugation K n g⁻¹ = (realLieConjugation K n g).symm := by
  apply LieEquiv.ext
  intro X
  apply (realLieConjugation K n g).injective
  have h := congrArg (fun e : RealLieAlgebra K n ≃ₗ⁅ℝ⁆ RealLieAlgebra K n => e X)
    (realLieConjugation_mul K n g g⁻¹)
  simpa using h.symm

/-- Extend the real adjoint map by the identity on complex coefficients. -/
def complexLieConjugation (g : InfiniteAdelicGL K n) :
    ComplexLieAlgebra K n ≃ₗ⁅ℂ⁆ ComplexLieAlgebra K n :=
  { (realLieConjugation K n g).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (realLieConjugation K n g).toLieHom).map_lie X Y }

@[simp]
theorem complexLieConjugation_tmul (g : InfiniteAdelicGL K n)
    (z : ℂ) (X : RealLieAlgebra K n) :
    complexLieConjugation K n g (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] realLieConjugation K n g X := rfl

@[simp]
theorem complexLieConjugation_complexify (g : InfiniteAdelicGL K n)
    (X : RealLieAlgebra K n) :
    complexLieConjugation K n g (complexify K n X) =
      complexify K n (realLieConjugation K n g X) := rfl

@[simp]
theorem complexLieConjugation_one :
    complexLieConjugation K n 1 = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

theorem complexLieConjugation_mul (g h : InfiniteAdelicGL K n) :
    complexLieConjugation K n (g * h) =
      (complexLieConjugation K n h).trans (complexLieConjugation K n g) := by
  apply LieEquiv.ext
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp [realLieConjugation_mul]
  | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

@[simp]
theorem complexLieConjugation_inv (g : InfiniteAdelicGL K n) :
    complexLieConjugation K n g⁻¹ = (complexLieConjugation K n g).symm := by
  apply LieEquiv.ext
  intro X
  apply (complexLieConjugation K n g).injective
  have h := congrArg (fun e : ComplexLieAlgebra K n ≃ₗ⁅ℂ⁆ ComplexLieAlgebra K n => e X)
    (complexLieConjugation_mul K n g g⁻¹)
  simpa using h.symm

attribute [local instance 100] LieRing.ofAssociativeRing

private def envelopingConjugationHom (g : InfiniteAdelicGL K n) :
    EnvelopingAlgebra K n →ₐ[ℂ] EnvelopingAlgebra K n :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((envelopingGenerator K n).comp (complexLieConjugation K n g).toLieHom)

private theorem envelopingConjugationHom_generator (g : InfiniteAdelicGL K n)
    (X : ComplexLieAlgebra K n) :
    envelopingConjugationHom K n g (envelopingGenerator K n X) =
      envelopingGenerator K n (complexLieConjugation K n g X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ _ X

private theorem envelopingConjugationHom_one :
    envelopingConjugationHom K n 1 = AlgHom.id ℂ (EnvelopingAlgebra K n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingConjugationHom K n 1 (envelopingGenerator K n X) =
    envelopingGenerator K n X
  rw [envelopingConjugationHom_generator, complexLieConjugation_one]
  rfl

private theorem envelopingConjugationHom_mul (g h : InfiniteAdelicGL K n) :
    envelopingConjugationHom K n (g * h) =
      (envelopingConjugationHom K n g).comp (envelopingConjugationHom K n h) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingConjugationHom K n (g * h) (envelopingGenerator K n X) =
    envelopingConjugationHom K n g
      (envelopingConjugationHom K n h (envelopingGenerator K n X))
  simp only [envelopingConjugationHom_generator, complexLieConjugation_mul,
    LieEquiv.trans_apply]

/-- The actual universal enveloping lift of the complex adjoint automorphism. -/
def envelopingConjugation (g : InfiniteAdelicGL K n) :
    EnvelopingAlgebra K n ≃ₐ[ℂ] EnvelopingAlgebra K n :=
  { envelopingConjugationHom K n g with
    invFun := envelopingConjugationHom K n g⁻¹
    left_inv := by
      intro a
      have h : (envelopingConjugationHom K n g⁻¹).comp
          (envelopingConjugationHom K n g) = AlgHom.id ℂ (EnvelopingAlgebra K n) := by
        rw [← envelopingConjugationHom_mul, inv_mul_cancel, envelopingConjugationHom_one]
      exact AlgHom.congr_fun h a
    right_inv := by
      intro a
      have h : (envelopingConjugationHom K n g).comp
          (envelopingConjugationHom K n g⁻¹) = AlgHom.id ℂ (EnvelopingAlgebra K n) := by
        rw [← envelopingConjugationHom_mul, mul_inv_cancel, envelopingConjugationHom_one]
      exact AlgHom.congr_fun h a }

@[simp]
theorem envelopingConjugation_generator (g : InfiniteAdelicGL K n)
    (X : ComplexLieAlgebra K n) :
    envelopingConjugation K n g (envelopingGenerator K n X) =
      envelopingGenerator K n (complexLieConjugation K n g X) :=
  envelopingConjugationHom_generator K n g X

@[simp]
theorem envelopingConjugation_one :
    envelopingConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  exact AlgHom.congr_fun (envelopingConjugationHom_one K n) a

theorem envelopingConjugation_mul (g h : InfiniteAdelicGL K n) :
    envelopingConjugation K n (g * h) =
      (envelopingConjugation K n h).trans (envelopingConjugation K n g) := by
  apply AlgEquiv.ext
  intro a
  exact AlgHom.congr_fun (envelopingConjugationHom_mul K n g h) a

@[simp]
theorem envelopingConjugation_inv (g : InfiniteAdelicGL K n) :
    envelopingConjugation K n g⁻¹ = (envelopingConjugation K n g).symm := by
  apply AlgEquiv.ext
  intro a
  rfl

/-- Restrict the actual enveloping automorphism to its algebra center. -/
def centerConjugation (g : InfiniteAdelicGL K n) :
    EnvelopingCenter K n ≃ₐ[ℂ] EnvelopingCenter K n where
  toFun z := ⟨envelopingConjugation K n g z.val,
    Subalgebra.map_center_le_center (envelopingConjugation K n g).surjective
      ⟨z.val, z.property, rfl⟩⟩
  invFun z := ⟨(envelopingConjugation K n g).symm z.val,
    Subalgebra.map_center_le_center (envelopingConjugation K n g).symm.surjective
      ⟨z.val, z.property, rfl⟩⟩
  left_inv z := Subtype.ext ((envelopingConjugation K n g).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((envelopingConjugation K n g).apply_symm_apply z.val)
  map_mul' z w := Subtype.ext (map_mul (envelopingConjugation K n g) z.val w.val)
  map_add' z w := Subtype.ext (map_add (envelopingConjugation K n g) z.val w.val)
  commutes' c := Subtype.ext ((envelopingConjugation K n g).commutes c)

@[simp]
theorem centerInclusion_centerConjugation (g : InfiniteAdelicGL K n)
    (z : EnvelopingCenter K n) :
    centerInclusion K n (centerConjugation K n g z) =
      envelopingConjugation K n g (centerInclusion K n z) := rfl

@[simp]
theorem centerConjugation_one :
    centerConjugation K n 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change envelopingConjugation K n 1 z.val = z.val
  rw [envelopingConjugation_one]
  rfl

theorem centerConjugation_mul (g h : InfiniteAdelicGL K n) :
    centerConjugation K n (g * h) =
      (centerConjugation K n h).trans (centerConjugation K n g) := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change envelopingConjugation K n (g * h) z.val =
    envelopingConjugation K n g (envelopingConjugation K n h z.val)
  rw [envelopingConjugation_mul]
  rfl

@[simp]
theorem centerConjugation_inv (g : InfiniteAdelicGL K n) :
    centerConjugation K n g⁻¹ = (centerConjugation K n g).symm := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  rfl

end Langlands.Global.ArchimedeanGL
