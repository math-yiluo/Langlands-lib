import Langlands.Global.ArchimedeanOrbitDerivativeInterchange

/-! # Genuine differentiation of continuous scalar orbit coefficients -/

noncomputable section
universe u
open scoped Classical Topology Manifold ContDiff Matrix.Norms.Operator
open Filter Set TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem matrixRightOrbit_normedDerivative_fderiv
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (s : Compacts (InfiniteAdelicGL K n)) (g : ArchimedeanGL K n)
    (X : RealLieAlgebra K n) :
    fderiv ℝ
        (fun y => DerivativeSmoothFunctions.normedDerivativeCoordinates K n
          (matrixRightOrbit K n f y) (a, s))
        (g : ArchimedeanMatrix K n)
        ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X) =
      DerivativeSmoothFunctions.normedDerivativeCoordinates K n
        (matrixRightOrbit K n
          (DerivativeSmoothFunctions.operator K n
            (envelopingGenerator K n (complexify K n X)) f)
          (g : ArchimedeanMatrix K n)) (a, s) := by
  let A := fun y => DerivativeSmoothFunctions.normedDerivativeCoordinates K n
    (matrixRightOrbit K n f y) (a, s)
  have hA : DifferentiableAt ℝ A (g : ArchimedeanMatrix K n) :=
    ((matrixRightOrbit_normedDerivative_contDiffOn K n f a s).contDiffAt
      ((isOpen_matrixUnitDomain K n).mem_nhds ⟨g, rfl⟩)).differentiableAt (by simp)
  apply ContinuousMap.ext
  intro x
  have heval := (ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp
    (g : ArchimedeanMatrix K n) hA.hasFDerivAt
  have hpoint :
      (fun y => A y x) = fun y => matrixDerivativeRightOrbitValue K n f a
        (y, (archimedeanGLCoordinates K n x.val : ArchimedeanMatrix K n)) := by
    funext y
    change (envelopingAction K n a (DerivativeSmoothFunctions.toSmooth K n
      (matrixRightOrbit K n f y))).val x.val = _
    simp only [matrixDerivativeRightOrbitValue, coordinateExtension_apply,
      ContinuousMulEquiv.symm_apply_apply]
  have h := congrArg
    (fun L => L ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X))
    heval.fderiv
  have hh :
      fderiv ℝ (fun y => A y x) (g : ArchimedeanMatrix K n)
          ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X) =
        (fderiv ℝ A (g : ArchimedeanMatrix K n)
          ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply] using h
  rw [hpoint, matrixDerivativeRightOrbitValue_parameter_derivative] at hh
  change (fderiv ℝ A (g : ArchimedeanMatrix K n)
    ((g : ArchimedeanMatrix K n) * realLieAlgebraToMatrix K n X)) x =
      (envelopingAction K n a (DerivativeSmoothFunctions.toSmooth K n
        (matrixRightOrbit K n
          (DerivativeSmoothFunctions.operator K n
            (envelopingGenerator K n (complexify K n X)) f)
          (g : ArchimedeanMatrix K n)))).val x.val
  simpa only [matrixDerivativeRightOrbitValue, coordinateExtension_apply,
    ContinuousMulEquiv.symm_apply_apply] using hh.symm

/-- An arbitrary continuous scalar functional commutes with the actual real
directional derivative of its positive right-translation orbit. -/
theorem smoothDifferential_smoothOrbitCoefficient
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n) (X : RealLieAlgebra K n) :
    smoothDifferential K n X (smoothOrbitCoefficient K n ℓ f) =
      smoothOrbitCoefficient K n ℓ
        (DerivativeSmoothFunctions.operator K n
          (envelopingGenerator K n (complexify K n X)) f) := by
  apply Subtype.ext
  funext g
  have hext (h : ArchimedeanGL K n) :
      ℓ (matrixRightOrbit K n f (h : ArchimedeanMatrix K n)) =
        (smoothOrbitCoefficient K n ℓ f).val
          ((archimedeanGLCoordinates K n).symm h) := by
    rw [matrixRightOrbit_apply, smoothOrbitCoefficient_apply]
  rw [smoothDifferential_eq_of_extension K n X (smoothOrbitCoefficient K n ℓ f)
    (fun y => ℓ (matrixRightOrbit K n f y)) hext]
  have h := Langlands.Analysis.fderiv_scalar_of_product_embedding_apply
    (DerivativeSmoothFunctions.normedDerivativeCoordinates K n)
    (DerivativeSmoothFunctions.isEmbedding_normedDerivativeCoordinates K n)
    (ℓ.restrictScalars ℝ)
    (f := matrixRightOrbit K n f)
    (x := (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))
    (d := (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
      realLieAlgebraToMatrix K n X)
    (v := matrixRightOrbit K n
      (DerivativeSmoothFunctions.operator K n
        (envelopingGenerator K n (complexify K n X)) f)
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))
    (fun i => ((matrixRightOrbit_normedDerivative_contDiffOn K n f i.1 i.2).contDiffAt
      ((isOpen_matrixUnitDomain K n).mem_nhds ⟨_, rfl⟩)).differentiableAt (by simp))
    (fun i => matrixRightOrbit_normedDerivative_fderiv K n f i.1 i.2 _ X)
  simpa only [ContinuousLinearMap.coe_restrictScalars', matrixRightOrbit_apply,
    smoothOrbitCoefficient_apply, ContinuousMulEquiv.symm_apply_apply] using h

/-- The coefficient depends complex-linearly on its actual smooth vector. -/
def smoothOrbitCoefficientLinear
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ) :
    DerivativeSmoothFunctions K n →ₗ[ℂ] SmoothFunctions K n where
  toFun := smoothOrbitCoefficient K n ℓ
  map_add' f h := by
    apply Subtype.ext
    funext g
    simp only [smoothOrbitCoefficient_apply, derivativeRightOrbit, map_add,
      Submodule.coe_add, Pi.add_apply]
  map_smul' z f := by
    apply Subtype.ext
    funext g
    simp only [smoothOrbitCoefficient_apply, derivativeRightOrbit, map_smul,
      Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]

theorem smoothOrbitCoefficient_add
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f h : DerivativeSmoothFunctions K n) :
    smoothOrbitCoefficient K n ℓ (f + h) =
      smoothOrbitCoefficient K n ℓ f + smoothOrbitCoefficient K n ℓ h :=
  (smoothOrbitCoefficientLinear K n ℓ).map_add f h

theorem smoothOrbitCoefficient_smul
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (z : ℂ) (f : DerivativeSmoothFunctions K n) :
    smoothOrbitCoefficient K n ℓ (z • f) = z • smoothOrbitCoefficient K n ℓ f :=
  (smoothOrbitCoefficientLinear K n ℓ).map_smul z f

theorem derivativeOperator_one (f : DerivativeSmoothFunctions K n) :
    DerivativeSmoothFunctions.operator K n 1 f = f := by
  apply (DerivativeSmoothFunctions.toSmooth K n).injective
  simp only [DerivativeSmoothFunctions.toSmooth_operator, envelopingAction_one]

theorem derivativeOperator_add (a b : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    DerivativeSmoothFunctions.operator K n (a + b) f =
      DerivativeSmoothFunctions.operator K n a f +
        DerivativeSmoothFunctions.operator K n b f := by
  apply (DerivativeSmoothFunctions.toSmooth K n).injective
  simp only [map_add, DerivativeSmoothFunctions.toSmooth_operator, LinearMap.add_apply]

theorem derivativeOperator_smul (z : ℂ) (a : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    DerivativeSmoothFunctions.operator K n (z • a) f =
      z • DerivativeSmoothFunctions.operator K n a f := by
  apply (DerivativeSmoothFunctions.toSmooth K n).injective
  simp only [map_smul, DerivativeSmoothFunctions.toSmooth_operator, LinearMap.smul_apply]

theorem derivativeOperator_mul (a b : EnvelopingAlgebra K n)
    (f : DerivativeSmoothFunctions K n) :
    DerivativeSmoothFunctions.operator K n (a * b) f =
      DerivativeSmoothFunctions.operator K n a
        (DerivativeSmoothFunctions.operator K n b f) := by
  apply (DerivativeSmoothFunctions.toSmooth K n).injective
  simp only [DerivativeSmoothFunctions.toSmooth_operator, envelopingAction_mul]

/-- Every actual complex enveloping operator acts inside the scalar coefficient,
with the original order of multiplication. -/
theorem envelopingAction_smoothOrbitCoefficient
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (a : EnvelopingAlgebra K n) (f : DerivativeSmoothFunctions K n) :
    envelopingAction K n a (smoothOrbitCoefficient K n ℓ f) =
      smoothOrbitCoefficient K n ℓ (DerivativeSmoothFunctions.operator K n a f) := by
  let P : EnvelopingAlgebra K n → Prop := fun b =>
    ∀ v : DerivativeSmoothFunctions K n,
      envelopingAction K n b (smoothOrbitCoefficient K n ℓ v) =
        smoothOrbitCoefficient K n ℓ (DerivativeSmoothFunctions.operator K n b v)
  suffices h : P a from h f
  apply enveloping_real_left_induction K n
  · intro v
    rw [envelopingAction_one, derivativeOperator_one]
  · intro b c hb hc v
    rw [map_add, LinearMap.add_apply, derivativeOperator_add,
      smoothOrbitCoefficient_add, hb v, hc v]
  · intro z b hb v
    rw [map_smul, LinearMap.smul_apply, derivativeOperator_smul,
      smoothOrbitCoefficient_smul, hb v]
  · intro X b hb v
    rw [envelopingAction_mul, hb v, envelopingAction_real_generator,
      smoothDifferential_smoothOrbitCoefficient, derivativeOperator_mul]

theorem envelopingAction_smoothOrbitCoefficient_apply
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (a : EnvelopingAlgebra K n) (f : DerivativeSmoothFunctions K n)
    (g : InfiniteAdelicGL K n) :
    (envelopingAction K n a (smoothOrbitCoefficient K n ℓ f)).val g =
      ℓ ((DerivativeSmoothFunctions.toSmooth K n).symm
        (smoothRightAction K n g
          (envelopingAction K n a (DerivativeSmoothFunctions.toSmooth K n f)))) := by
  rw [envelopingAction_smoothOrbitCoefficient, smoothOrbitCoefficient_apply]
  rfl

end Langlands.Global.ArchimedeanGL
