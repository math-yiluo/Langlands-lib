import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticDifferential
import Langlands.Global.ArchimedeanFiniteVectorCalculus

/-! # Genuine coefficient orbit differentiation and its real Lie action -/

noncomputable section

universe uF

open scoped Classical Manifold ContDiff Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

private def representationContinuous (g : InfiniteAdelicGL F n) :
    Space e ρ →L[ℂ] Space e ρ :=
  (representation e ρ g).toContinuousLinearMap

private theorem leftTranslation_smoothOrbitMap (g : InfiniteAdelicGL F n) (v : Space e ρ) :
    finiteVectorSmoothLeftTranslation F n m g (smoothOrbitMap e ρ v) =
      vectorSmoothMap F n (m → ℂ)
        (representationContinuous e ρ g : (m → ℂ) →L[ℂ] (m → ℂ)) (smoothOrbitMap e ρ v) := by
  apply Subtype.ext
  funext x
  change representation e ρ (g * x) v = representation e ρ g (representation e ρ x v)
  rw [map_mul]
  rfl

/-- At the identity the genuine vector function differential is exactly the
actual Frechet coefficient differential, without an algebraic comparison premise. -/
theorem smoothOrbitMap_differential_one (X : RealLieAlgebra F n) (v : Space e ρ) :
    (finiteVectorSmoothDifferential F n m X (smoothOrbitMap e ρ v)).val 1 =
      analyticRealDifferential e ρ X v := by
  have hQ (h : ArchimedeanGL F n) :
      orbitCoordinateExtension e ρ v (h : ArchimedeanMatrix F n) =
        (smoothOrbitMap e ρ v).val ((archimedeanGLCoordinates F n).symm h) := by
    have h := orbitCoordinateExtension_apply e ρ v ((archimedeanGLCoordinates F n).symm h)
    simpa only [ContinuousMulEquiv.apply_symm_apply, smoothOrbitMap_apply] using h
  rw [finiteVectorSmoothDifferential_eq_of_extension F n m X _
    (orbitCoordinateExtension e ρ v) hQ]
  simp only [map_one, Units.val_one, one_mul]
  have hd := congrArg (fun D : ArchimedeanMatrix F n →L[ℝ] Space e ρ =>
    D (realLieAlgebraToMatrix F n X)) (hasFDerivAt_orbitCoordinateExtension e ρ v).fderiv
  exact hd.trans (orbitDerivative_realLie e ρ X v)

/-- The injective actual orbit map intertwines genuine function differentiation
with the constructed analytic coefficient differential at every group element. -/
theorem smoothOrbitMap_analyticRealDifferential (X : RealLieAlgebra F n) (v : Space e ρ) :
    smoothOrbitMap e ρ (analyticRealDifferential e ρ X v) =
      finiteVectorSmoothDifferential F n m X (smoothOrbitMap e ρ v) := by
  apply Subtype.ext
  funext g
  have hc := congrArg (fun f : VectorSmoothFunctions F n (m → ℂ) => f.val 1)
    (finiteVectorSmoothDifferential_leftTranslation F n m X g (smoothOrbitMap e ρ v))
  simp only [leftTranslation_smoothOrbitMap,
    finiteVectorSmoothLeftTranslation_apply, mul_one] at hc
  have hmap := finiteVectorSmoothDifferential_map F n m X
    (representationContinuous e ρ g : (m → ℂ) →L[ℂ] (m → ℂ)) (smoothOrbitMap e ρ v)
  have hc' := (congrArg (fun f : VectorSmoothFunctions F n (m → ℂ) => f.val 1) hmap).symm.trans hc
  exact (congrArg (representation e ρ g) (smoothOrbitMap_differential_one e ρ X v)).symm.trans hc'

/-- The real Lie law is derived from genuine orbit differentiation and
injectivity into the already constructed function differential representation. -/
def analyticRealLieAction : RealLieAlgebra F n →ₗ⁅ℝ⁆ Module.End ℂ (Space e ρ) :=
  { analyticRealDifferential e ρ with
    map_lie' := by
      intro X Y
      apply LinearMap.ext
      intro v
      apply smoothOrbitMap_injective e ρ
      change smoothOrbitMap e ρ (analyticRealDifferential e ρ ⁅X, Y⁆ v) =
        smoothOrbitMap e ρ (analyticRealDifferential e ρ X (analyticRealDifferential e ρ Y v) -
          analyticRealDifferential e ρ Y (analyticRealDifferential e ρ X v))
      simp only [map_sub, smoothOrbitMap_analyticRealDifferential]
      have h := (finiteVectorSmoothLieAction F n m).map_lie
        (complexify F n X) (complexify F n Y)
      rw [← (complexify F n).map_lie X Y] at h
      change finiteVectorSmoothDifferential F n m ⁅X, Y⁆ =
        finiteVectorSmoothDifferential F n m X * finiteVectorSmoothDifferential F n m Y -
          finiteVectorSmoothDifferential F n m Y * finiteVectorSmoothDifferential F n m X at h
      exact congrArg (fun T : Module.End ℂ (VectorSmoothFunctions F n (m → ℂ)) =>
        T (smoothOrbitMap e ρ v)) h }

@[simp]
theorem analyticRealLieAction_apply (X : RealLieAlgebra F n) (v : Space e ρ) :
    analyticRealLieAction e ρ X v = analyticRealDifferential e ρ X v := rfl

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
