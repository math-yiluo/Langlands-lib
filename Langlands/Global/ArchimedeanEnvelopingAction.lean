import Langlands.Global.ArchimedeanDifferentialLawsProof

/-! # The actual complex Lie and universal enveloping differential actions -/

noncomputable section
universe u
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The genuine matrix directional differential, bundled as a real Lie homomorphism. -/
def realSmoothLieAction :
    RealLieAlgebra K n →ₗ⁅ℝ⁆ Module.End ℂ (SmoothFunctions K n) :=
  { realSmoothDifferential K n with
    map_lie' := by
      intro X Y
      exact smoothDifferential_commutator K n X Y }

@[simp]
theorem realSmoothLieAction_apply (X : RealLieAlgebra K n) :
    realSmoothLieAction K n X = smoothDifferential K n X := rfl

/-- Complex-linear extension of the actual real directional differential. -/
def complexSmoothDifferential :
    ComplexLieAlgebra K n →ₗ[ℂ] Module.End ℂ (SmoothFunctions K n) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realSmoothDifferential K n))

@[simp]
theorem complexSmoothDifferential_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    complexSmoothDifferential K n (z ⊗ₜ[ℝ] X) = z • smoothDifferential K n X := rfl

/-- The complexified real matrix Lie algebra acts by the genuine differential operators. -/
def complexSmoothLieAction :
    ComplexLieAlgebra K n →ₗ⁅ℂ⁆ Module.End ℂ (SmoothFunctions K n) :=
  { complexSmoothDifferential K n with
    map_lie' := by
      intro U V
      change complexSmoothDifferential K n ⁅U, V⁆ =
        complexSmoothDifferential K n U * complexSmoothDifferential K n V -
          complexSmoothDifferential K n V * complexSmoothDifferential K n U
      induction U using TensorProduct.inductionOn with
      | tmul z X =>
        induction V using TensorProduct.inductionOn with
        | tmul w Y =>
          simp only [complexLieAlgebra_lie_tmul, complexSmoothDifferential_tmul]
          have h := smoothDifferential_commutator K n X Y
          change smoothDifferential K n ⁅X, Y⁆ =
            smoothDifferential K n X * smoothDifferential K n Y -
              smoothDifferential K n Y * smoothDifferential K n X at h
          rw [h]
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm w z]
          exact smul_sub (z * w)
            (smoothDifferential K n X * smoothDifferential K n Y)
            (smoothDifferential K n Y * smoothDifferential K n X)
        | add U V hU hV =>
          rw [LieRing.lie_add]
          simp only [map_add, hU, hV, mul_add, add_mul]
          abel
      | add U V hU hV =>
        simp only [add_lie, map_add, hU, hV, mul_add, add_mul]
        abel }


@[simp]
theorem complexSmoothLieAction_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    complexSmoothLieAction K n (z ⊗ₜ[ℝ] X) = z • smoothDifferential K n X := rfl

@[simp]
theorem complexSmoothLieAction_complexify (X : RealLieAlgebra K n) :
    complexSmoothLieAction K n (complexify K n X) = smoothDifferential K n X := by
  simp

/-- The universal enveloping algebra action extending the actual differential. -/
def envelopingAction : EnvelopingAlgebra K n →ₐ[ℂ] Module.End ℂ (SmoothFunctions K n) :=
  UniversalEnvelopingAlgebra.lift ℂ (complexSmoothLieAction K n)

@[simp]
theorem envelopingAction_generator (X : ComplexLieAlgebra K n) :
    envelopingAction K n (envelopingGenerator K n X) = complexSmoothLieAction K n X :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (complexSmoothLieAction K n) X

@[simp]
theorem envelopingAction_real_generator (X : RealLieAlgebra K n) :
    envelopingAction K n (envelopingGenerator K n (complexify K n X)) =
      smoothDifferential K n X := by simp

theorem envelopingAction_real_generator_apply (X : RealLieAlgebra K n)
    (f : SmoothFunctions K n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (envelopingAction K n (envelopingGenerator K n (complexify K n X)) f).val g =
      fderiv ℝ (coordinateExtension K n f)
        (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X) := by
  rw [envelopingAction_real_generator, smoothDifferential_apply]

@[simp]
theorem envelopingAction_one (f : SmoothFunctions K n) :
    envelopingAction K n 1 f = f := by simp

theorem envelopingAction_mul (a b : EnvelopingAlgebra K n) (f : SmoothFunctions K n) :
    envelopingAction K n (a * b) f =
      envelopingAction K n a (envelopingAction K n b f) := by
  rw [map_mul, Module.End.mul_apply]

/-- Restriction of the actual enveloping action to its algebra center. -/
def centerAction : EnvelopingCenter K n →ₐ[ℂ] Module.End ℂ (SmoothFunctions K n) :=
  (envelopingAction K n).comp (centerInclusion K n)

@[simp]
theorem centerAction_apply (z : EnvelopingCenter K n) :
    centerAction K n z = envelopingAction K n (centerInclusion K n z) := rfl

end Langlands.Global.ArchimedeanGL
