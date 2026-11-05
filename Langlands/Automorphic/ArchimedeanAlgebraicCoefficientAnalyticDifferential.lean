import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientSmooth
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialComparisonStatement

/-! # The actual real Frechet differential on archimedean algebraic coefficients -/

noncomputable section

universe uF

open scoped Classical Manifold ContDiff TensorProduct Matrix Matrix.Norms.Operator

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

/-- The same genuine oriented matrix embedding, as a continuous real linear map. -/
def embeddingMatrixLinear :
    ArchimedeanMatrix F n →L[ℝ] (I → Matrix (Fin n) (Fin n) ℂ) :=
  (embeddingMatrixHom F n e).toLinearMap.toContinuousLinearMap

omit [Fintype I] in
@[simp]
theorem embeddingMatrixLinear_apply (A : ArchimedeanMatrix F n) :
    embeddingMatrixLinear (n := n) e A = embeddingMatrixHom F n e A := rfl

private def matrixVectorEvaluation (v : Space e ρ) : Matrix m m ℂ →L[ℝ] Space e ρ :=
  ((Matrix.mulVecBilin ℝ ℂ).flip (v : m → ℂ)).toContinuousLinearMap

/-- An actual ambient expression for the coefficient orbit function. Its values
on invertible matrices are the original point action. -/
def orbitCoordinateExtension (v : Space e ρ) (A : ArchimedeanMatrix F n) : Space e ρ :=
  ρ.productMatrixCoordinateExtension (embeddingMatrixHom F n e A) *ᵥ (v : m → ℂ)

/-- The actual Frechet derivative at the identity of the coefficient orbit. -/
def orbitDerivative (v : Space e ρ) : ArchimedeanMatrix F n →L[ℝ] Space e ρ :=
  (matrixVectorEvaluation e ρ v).comp
    ((ρ.analyticProductDifferential (B := ℂ)).comp (embeddingMatrixLinear (n := n) e))

omit [NumberField F] in
@[simp]
theorem orbitCoordinateExtension_apply (v : Space e ρ) (g : InfiniteAdelicGL F n) :
    orbitCoordinateExtension e ρ v
      (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) = representation e ρ g v := by
  have h := ρ.productMatrixCoordinateExtension_apply (B := ℂ) (embeddingGL F n e g)
  simp only [embeddingGL_val] at h
  change ρ.productMatrixCoordinateExtension
    (embeddingMatrixHom F n e (archimedeanGLCoordinates F n g).val) *ᵥ (v : m → ℂ) = _
  change _ = (ρ.productMatrixPointsHom ℂ (embeddingGL F n e g) : Matrix m m ℂ) *ᵥ (v : m → ℂ)
  exact congrArg (fun A : Matrix m m ℂ => A *ᵥ (v : m → ℂ)) h

/-- This derivative is supplied by real calculus on the actual orbit extension,
without any analytic/algebraic differential comparison premise. -/
theorem hasFDerivAt_orbitCoordinateExtension (v : Space e ρ) :
    HasFDerivAt (𝕜 := ℝ) (orbitCoordinateExtension e ρ v) (orbitDerivative e ρ v)
      (1 : ArchimedeanMatrix F n) := by
  have he : embeddingMatrixLinear (n := n) e (1 : ArchimedeanMatrix F n) = 1 :=
    map_one (embeddingMatrixHom F n e)
  have hρ : HasFDerivAt (𝕜 := ℝ) (ρ.productMatrixCoordinateExtension (B := ℂ))
      (ρ.analyticProductDifferential (B := ℂ))
      (embeddingMatrixLinear (n := n) e (1 : ArchimedeanMatrix F n)) := by
    rw [he]
    exact ρ.hasFDerivAt_analyticProductDifferential
  have hcomp := hρ.comp (1 : ArchimedeanMatrix F n)
    (embeddingMatrixLinear (n := n) e).hasFDerivAt
  exact (matrixVectorEvaluation e ρ v).hasFDerivAt.comp (1 : ArchimedeanMatrix F n) hcomp

/-- The actual real infinitesimal coefficient endomorphism family. Its Lie law
is not part of this construction. -/
def analyticRealDifferential : RealLieAlgebra F n →ₗ[ℝ] Module.End ℂ (Space e ρ) :=
  ((Matrix.toLin' : Matrix m m ℂ ≃ₗ[ℂ] Module.End ℂ (m → ℂ)).toLinearMap.restrictScalars ℝ).comp
    ((ρ.analyticProductDifferential (B := ℂ)).toLinearMap.comp
      (embeddingRealLieHom F n e).toLinearMap)

omit [NumberField F] in
@[simp]
theorem analyticRealDifferential_apply (X : RealLieAlgebra F n) (v : Space e ρ) :
    analyticRealDifferential e ρ X v =
      ρ.analyticProductDifferential (B := ℂ) (embeddingRealLieHom F n e X) *ᵥ (v : m → ℂ) := rfl

/-- Evaluation on the original real matrix Lie direction recovers exactly the
constructed infinitesimal endomorphism family. -/
theorem orbitDerivative_realLie (X : RealLieAlgebra F n) (v : Space e ρ) :
    orbitDerivative e ρ v (realLieAlgebraToMatrix F n X) =
      analyticRealDifferential e ρ X v := rfl

omit [NumberField F] in
/-- The separately stated generic comparison is the precise remaining premise
for identification with the existing algebraic coefficient Lie action. -/
theorem analyticRealDifferential_eq_lie_of_comparison
    (h : MatrixRepresentation.AnalyticProductDifferentialComparison (B := ℂ) ρ)
    (X : RealLieAlgebra F n) (v : Space e ρ) :
    analyticRealDifferential e ρ X v = ⁅(1 : ℂ) ⊗ₜ[ℝ] X, v⁆ := by
  apply (coordinates e ρ).injective
  rw [coordinates_lie_tmul, one_smul]
  change ρ.analyticProductDifferential (B := ℂ) (embeddingRealLieHom F n e X) *ᵥ
    (v : m → ℂ) = _
  rw [h]
  rfl

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
