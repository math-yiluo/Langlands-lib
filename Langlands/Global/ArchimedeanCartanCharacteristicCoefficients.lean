import Langlands.Global.ArchimedeanCartanDiagonalRestriction
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Actual archimedean matrix characteristic coefficients -/

noncomputable section
universe u
open scoped TensorProduct
open NumberField
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- The real and complex matrix factors, with a chosen complex coefficient field. -/
abbrev CartanCharacteristicPlace :=
  Sum {v : InfinitePlace K // v.IsReal} {v : InfinitePlace K // v.IsComplex}

/-- Project actual mixed matrices to a complex matrix at an infinite place. -/
def archimedeanPlaceMatrixHom (v : CartanCharacteristicPlace K) :
    ArchimedeanMatrix K n →+* Matrix (Fin n) (Fin n) ℂ :=
  match v with
  | .inl v =>
      (Complex.ofRealHom.comp
        ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsReal} => ℝ) v).comp
          (RingHom.fst _ _))).mapMatrix
  | .inr v =>
      ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // v.IsComplex} => ℂ) v).comp
        (RingHom.snd _ _)).mapMatrix

/-- Real-linear matrix coordinates of the actual real Lie algebra. -/
def realLiePlaceMatrix (v : CartanCharacteristicPlace K) :
    RealLieAlgebra K n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := archimedeanPlaceMatrixHom K n v (realLieAlgebraToMatrix K n X)
  map_add' X Y := by simp
  map_smul' r X := by
    rw [map_smul]
    ext i j
    cases v <;> simp [archimedeanPlaceMatrixHom, Matrix.smul_apply, smul_eq_mul]

/-- Complex-linear extension of one actual matrix factor. -/
def complexLiePlaceMatrix (v : CartanCharacteristicPlace K) :
    ComplexLieAlgebra K n →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realLiePlaceMatrix K n v))

@[simp]
theorem complexLiePlaceMatrix_tmul (v : CartanCharacteristicPlace K)
    (z : ℂ) (X : RealLieAlgebra K n) :
    complexLiePlaceMatrix K n v (z ⊗ₜ[ℝ] X) = z • realLiePlaceMatrix K n v X := rfl

/-- Individual actual complex-linear coordinate functionals. -/
def liePlaceCoordinate (v : CartanCharacteristicPlace K) (i j : Fin n) :
    Module.Dual ℂ (ComplexLieAlgebra K n) where
  toFun X := complexLiePlaceMatrix K n v X i j
  map_add' X Y := by simp
  map_smul' z X := by simp

/-- The universal polynomial matrix with actual Lie coordinate entries. -/
def lieGenericPlaceMatrix (v : CartanCharacteristicPlace K) :
    Matrix (Fin n) (Fin n) (LiePolynomialAlgebra K n) :=
  fun i j => SymmetricAlgebra.ι ℂ _ (liePlaceCoordinate K n v i j)

/-- A characteristic coefficient of an actual full-Lie polynomial matrix. -/
def lieCharacteristicCoefficient (v : CartanCharacteristicPlace K) (r : ℕ) :
    LiePolynomialAlgebra K n :=
  (lieGenericPlaceMatrix K n v).charpoly.coeff r

theorem lieGenericPlaceMatrix_evaluation (v : CartanCharacteristicPlace K)
    (X : ComplexLieAlgebra K n) :
    (lieGenericPlaceMatrix K n v).map (liePolynomialEvaluation K n X) =
      complexLiePlaceMatrix K n v X := by
  ext i j
  simp [lieGenericPlaceMatrix, liePlaceCoordinate]

theorem lieCharacteristicCoefficient_evaluation (v : CartanCharacteristicPlace K)
    (r : ℕ) (X : ComplexLieAlgebra K n) :
    liePolynomialEvaluation K n X (lieCharacteristicCoefficient K n v r) =
      (complexLiePlaceMatrix K n v X).charpoly.coeff r := by
  change (liePolynomialEvaluation K n X).toRingHom
    ((lieGenericPlaceMatrix K n v).charpoly.coeff r) = _
  rw [← Polynomial.coeff_map, ← Matrix.charpoly_map]
  change ((lieGenericPlaceMatrix K n v).map (liePolynomialEvaluation K n X)).charpoly.coeff r = _
  rw [lieGenericPlaceMatrix_evaluation]

theorem realLiePlaceMatrix_conjugation (v : CartanCharacteristicPlace K)
    (g : InfiniteAdelicGL K n) (X : RealLieAlgebra K n) :
    realLiePlaceMatrix K n v (realLieConjugation K n g X) =
      (archimedeanPlaceMatrixHom K n v (archimedeanGLCoordinates K n g).val) *
        realLiePlaceMatrix K n v X *
        (archimedeanPlaceMatrixHom K n v (archimedeanGLCoordinates K n g⁻¹).val) := by
  change archimedeanPlaceMatrixHom K n v
    (realLieAlgebraToMatrix K n (realLieConjugation K n g X)) = _
  rw [realLieAlgebraToMatrix_realLieConjugation, map_mul, map_mul]
  rfl

theorem realLiePlaceMatrix_conjugation_charpoly (v : CartanCharacteristicPlace K)
    (g : InfiniteAdelicGL K n) (X : RealLieAlgebra K n) :
    (realLiePlaceMatrix K n v (realLieConjugation K n g X)).charpoly =
      (realLiePlaceMatrix K n v X).charpoly := by
  have hi : archimedeanPlaceMatrixHom K n v (archimedeanGLCoordinates K n g⁻¹).val *
      archimedeanPlaceMatrixHom K n v (archimedeanGLCoordinates K n g).val = 1 := by
    rw [← map_mul, map_inv, Units.inv_mul, map_one]
  rw [realLiePlaceMatrix_conjugation, Matrix.charpoly_mul_comm, ← mul_assoc, hi, one_mul]

/-- These concrete characteristic coefficients are fixed by the entire actual group. -/
theorem lieCharacteristicCoefficient_invariant [NumberField K]
    (v : CartanCharacteristicPlace K) (r : ℕ) (g : InfiniteAdelicGL K n) :
    liePolynomialConjugation K n g (lieCharacteristicCoefficient K n v r) =
      lieCharacteristicCoefficient K n v r := by
  apply liePolynomial_ext_real K n
  intro X
  simp only [liePolynomialConjugation_evaluation, lieCharacteristicCoefficient_evaluation,
    complexLieConjugation_tmul, complexLiePlaceMatrix_tmul, one_smul,
    realLiePlaceMatrix_conjugation_charpoly]

/-- Restrict full-Lie polynomial functions to the actual diagonal subspace. -/
def lieDiagonalPolynomialRestriction :
    LiePolynomialAlgebra K n →ₐ[ℂ] CartanDiagonalPolynomialAlgebra K n :=
  (cartanDiagonalPolynomialRestriction K n).comp (cartanPolynomialRestriction K n)

/-- The diagonal coordinate dual to the actual entry at the chosen place. -/
def cartanDiagonalCoordinateDual (v : CartanCharacteristicPlace K) (i : Fin n) :
    Module.Dual ℂ (ComplexCartanDiagonal K n) :=
  (liePlaceCoordinate K n v i i).comp
    ((cartanComplexInclusion K n).comp (cartanDiagonalComplexInclusion K n))

/-- The corresponding coordinate generator in the diagonal polynomial algebra. -/
def cartanDiagonalCoordinate (v : CartanCharacteristicPlace K) (i : Fin n) :
    CartanDiagonalPolynomialAlgebra K n :=
  SymmetricAlgebra.ι ℂ _ (cartanDiagonalCoordinateDual K n v i)

theorem realLiePlaceMatrix_diagonal (v : CartanCharacteristicPlace K)
    (t : RealCartanDiagonal K n) :
    realLiePlaceMatrix K n v (cartanDiagonalInclusion K n t) =
      Matrix.diagonal (fun i =>
        match v with
        | .inl v => (t.1 v i : ℂ)
        | .inr v => (t.2 v i : ℂ)) := by
  change archimedeanPlaceMatrixHom K n v
    (realLieAlgebraToMatrix K n (cartanDiagonalInclusion K n t)) = _
  rw [cartanDiagonalInclusion_matrix]
  ext i j
  cases v <;> by_cases hij : i = j <;>
    simp [archimedeanPlaceMatrixHom, hij]

theorem cartanDiagonalCoordinateDual_tmul (v : CartanCharacteristicPlace K)
    (i : Fin n) (z : ℂ) (t : RealCartanDiagonal K n) :
    cartanDiagonalCoordinateDual K n v i (z ⊗ₜ[ℝ] t) =
      z * (match v with
        | .inl v => (t.1 v i : ℂ)
        | .inr v => (t.2 v i : ℂ)) := by
  change complexLiePlaceMatrix K n v
    (z ⊗ₜ[ℝ] (cartanDiagonalInclusion K n t : RealLieAlgebra K n)) i i = _
  rw [complexLiePlaceMatrix_tmul, realLiePlaceMatrix_diagonal]
  simp [Matrix.smul_apply, smul_eq_mul]

theorem liePlaceCoordinate_diagonal (v : CartanCharacteristicPlace K)
    (i j : Fin n) :
    (liePlaceCoordinate K n v i j).comp
      ((cartanComplexInclusion K n).comp (cartanDiagonalComplexInclusion K n)) =
        if i = j then cartanDiagonalCoordinateDual K n v i else 0 := by
  classical
  apply TensorProduct.AlgebraTensorModule.ext
  intro z t
  change complexLiePlaceMatrix K n v
      (z ⊗ₜ[ℝ] (cartanDiagonalInclusion K n t : RealLieAlgebra K n)) i j = _
  rw [complexLiePlaceMatrix_tmul, realLiePlaceMatrix_diagonal]
  by_cases hij : i = j
  · subst j
    simp [cartanDiagonalCoordinateDual_tmul, Matrix.smul_apply, smul_eq_mul]
  · simp [hij, Matrix.smul_apply]

theorem lieGenericPlaceMatrix_diagonal_restriction (v : CartanCharacteristicPlace K) :
    (lieGenericPlaceMatrix K n v).map (lieDiagonalPolynomialRestriction K n) =
      Matrix.diagonal (cartanDiagonalCoordinate K n v) := by
  classical
  ext i j
  change cartanDiagonalPolynomialRestriction K n
    (cartanPolynomialRestriction K n (SymmetricAlgebra.ι ℂ _ (liePlaceCoordinate K n v i j))) = _
  rw [cartanPolynomialRestriction_ι, cartanDiagonalPolynomialRestriction_ι,
    LinearMap.comp_assoc, liePlaceCoordinate_diagonal]
  by_cases hij : i = j
  · subst j
    simp [cartanDiagonalCoordinate]
  · simp [hij]

/-- Restricting the actual characteristic polynomial gives the diagonal product. -/
theorem lieCharacteristicPolynomial_diagonal_restriction
    (v : CartanCharacteristicPlace K) :
    (lieGenericPlaceMatrix K n v).charpoly.map
        (lieDiagonalPolynomialRestriction K n).toRingHom =
      ∏ i, (Polynomial.X - Polynomial.C (cartanDiagonalCoordinate K n v i)) := by
  rw [← Matrix.charpoly_map]
  change ((lieGenericPlaceMatrix K n v).map
    (lieDiagonalPolynomialRestriction K n)).charpoly = _
  rw [lieGenericPlaceMatrix_diagonal_restriction, Matrix.charpoly_diagonal]

theorem lieCharacteristicCoefficient_diagonal_restriction
    (v : CartanCharacteristicPlace K) (r : ℕ) :
    lieDiagonalPolynomialRestriction K n (lieCharacteristicCoefficient K n v r) =
      (∏ i, (Polynomial.X -
        Polynomial.C (cartanDiagonalCoordinate K n v i))).coeff r := by
  change (lieDiagonalPolynomialRestriction K n).toRingHom
    ((lieGenericPlaceMatrix K n v).charpoly.coeff r) = _
  rw [← Polynomial.coeff_map, lieCharacteristicPolynomial_diagonal_restriction]

/-- The concrete characteristic coefficient as an actual full-group fixed tensor. -/
def lieCharacteristicSymmetricInvariant [NumberField K]
    (v : CartanCharacteristicPlace K) (r : ℕ) : lieSymmetricGroupInvariants K n :=
  ⟨(lieSymmetricTraceEquiv K n).symm (lieCharacteristicCoefficient K n v r), by
    intro g
    apply (lieSymmetricTraceEquiv K n).injective
    rw [lieSymmetricTraceEquiv_conjugation, AlgEquiv.apply_symm_apply,
      lieCharacteristicCoefficient_invariant]⟩

/-- The invariant tensor's actual projected diagonal restriction is the expected coefficient. -/
theorem lieCharacteristicSymmetricInvariant_diagonal_restriction [NumberField K]
    (v : CartanCharacteristicPlace K) (r : ℕ) :
    cartanCompactInvariantDiagonalRestriction K n
        (cartanGroupInvariantRestriction K n (lieCharacteristicSymmetricInvariant K n v r)) =
      (∏ i, (Polynomial.X -
        Polynomial.C (cartanDiagonalCoordinate K n v i))).coeff r := by
  rw [cartanCompactInvariantDiagonalRestriction_apply, cartanGroupInvariantRestriction_coe,
    cartanSymmetricTraceEquiv_projection]
  change lieDiagonalPolynomialRestriction K n
    (lieSymmetricTraceEquiv K n
      ((lieSymmetricTraceEquiv K n).symm (lieCharacteristicCoefficient K n v r))) = _
  rw [AlgEquiv.apply_symm_apply, lieCharacteristicCoefficient_diagonal_restriction]

end Langlands.Global.ArchimedeanGL
