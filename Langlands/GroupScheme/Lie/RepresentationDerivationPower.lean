import Langlands.GroupScheme.Lie.TranslationDerivation
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.CommutativeAlgebra.DerivationPower

/-! # Translation derivations on actual representation coefficients -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Lie GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {n : ℕ}
  (ρ : MatrixRepresentation G (Fin n))

/-- The universal matrix of actual representation coefficients. -/
def coordinateMatrix : Matrix (Fin n) (Fin n) (coordinateAlgebra G) :=
  (ρ.affineMatrix (coordinateAlgebra G) (universalPoint G)).val

/-- Evaluating universal coefficients gives the actual matrix at any test point. -/
theorem coordinateMatrix_map {A : Type u} [CommRing A] [Algebra R A]
    (g : AffinePoints G A) :
    (coordinateMatrix ρ).map (pointCoordinates G g) =
      (ρ.affineMatrix (CommAlgCat.of R A) g).val := by
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (pointCoordinates G g)) (universalPoint G)
  change ρ.affineMatrix _ (affineMap G (pointCoordinates G g) (universalPoint G)) = _ at h
  rw [affineMap_universalPoint, Equiv.symm_apply_apply] at h
  exact (congrArg (fun z => z.val) h).symm

@[simp] theorem coordinateMatrix_origin :
    (coordinateMatrix ρ).map (coordinateOrigin G) = 1 := by
  simpa only [coordinateOrigin, map_one, Matrix.GeneralLinearGroup.coe_one] using
    coordinateMatrix_map ρ (1 : AffinePoints G R)

/-- Tangent matrices are the epsilon coefficients of the universal matrix. -/
theorem tangentMatrix_eq_coordinateMatrix (X : lieKernel G R) :
    ρ.tangentMatrix R X =
      (coordinateMatrix ρ).map (fun c => (pointCoordinates G X.val c).snd) := by
  ext i j
  have h := congrArg (fun M => (M i j).snd) (coordinateMatrix_map ρ X.val)
  rw [affineMatrix_lieKernel, matrixUnit_val, Matrix.add_apply,
    TrivSqZeroExt.snd_add, epsilonMatrix_apply, TrivSqZeroExt.snd_inr] at h
  have hz : ((1 : Matrix (Fin n) (Fin n) (DualNumber R)) i j).snd = 0 := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simpa only [hz, zero_add, Matrix.map_apply] using h.symm

omit [IsAffineHom G.X.hom] in
/-- A constant dual-number point has the entrywise constant representation matrix. -/
theorem affineMatrix_constant {A : Type u} [CommRing A] [Algebra R A]
    (g : AffinePoints G A) :
    (ρ.affineMatrix (CommAlgCat.of R (DualNumber A)) (constant G g)).val =
      (ρ.affineMatrix (CommAlgCat.of R A) g).val.map (TrivSqZeroExt.inlHom A A) := by
  exact congrArg (fun z => z.val)
    (ρ.affineMatrix_naturality
      (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R A A)) g)

/-- Differentiation of the universal representation matrix is left
multiplication by the coefficient-extended tangent matrix. -/
theorem coordinateMatrix_translationDerivation (X : lieKernel G R) :
    (coordinateMatrix ρ).map (translationDerivation G X) =
      (ρ.tangentMatrix R X).map (algebraMap R (coordinateAlgebra G)) *
        coordinateMatrix ρ := by
  have h := coordinateMatrix_map ρ
    (infinitesimalTranslate G X (universalPoint G))
  have hc : ρ.affineMatrix _ (constant G (universalPoint G)) =
      Matrix.GeneralLinearGroup.map
        (TrivSqZeroExt.inlHom (coordinateAlgebra G) (coordinateAlgebra G))
        (ρ.affineMatrix (coordinateAlgebra G) (universalPoint G)) :=
    ρ.affineMatrix_naturality
      (CommAlgCat.ofHom
        (TrivSqZeroExt.inlAlgHom R (coordinateAlgebra G) (coordinateAlgebra G)))
      (universalPoint G)
  rw [infinitesimalTranslate] at h
  rw [(ρ.affineMatrix _).map_mul, hc, Units.val_mul, affineMatrix_lieKernel,
    matrixUnit_val, tangentMatrix_naturality] at h
  change _ = (1 + epsilonMatrix
    ((ρ.tangentMatrix R X).map (algebraMap R (coordinateAlgebra G)))) *
      (coordinateMatrix ρ).map
        (TrivSqZeroExt.inlHom (coordinateAlgebra G) (coordinateAlgebra G)) at h
  rw [add_mul, one_mul, epsilonMatrix_mul_constantMatrix] at h
  ext i j
  have he := congrArg (fun M => (M i j).snd) h
  simpa only [Matrix.map_apply, translationDerivation_apply, translationLift,
    Matrix.add_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.inlHom_apply,
    TrivSqZeroExt.snd_inl, epsilonMatrix_apply, TrivSqZeroExt.snd_inr, zero_add,
    coordinateMatrix, infinitesimalTranslate, Algebra.ofId] using he

/-- Every base-linear map commutes with left multiplication by a matrix
whose entries come from the base ring. -/
theorem map_linearMap_constant_mul
    (f : coordinateAlgebra G →ₗ[R] coordinateAlgebra G)
    (M : Matrix (Fin n) (Fin n) R)
    (U : Matrix (Fin n) (Fin n) (coordinateAlgebra G)) :
    (M.map (algebraMap R (coordinateAlgebra G)) * U).map f =
      M.map (algebraMap R (coordinateAlgebra G)) * U.map f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Algebra.smul_def] using f.map_smul (M i a) (U a j)

/-- Every composition iterate acts on coefficients by the corresponding
matrix power, including exponent zero. -/
theorem coordinateMatrix_translationDerivation_pow (X : lieKernel G R) (m : ℕ) :
    (coordinateMatrix ρ).map ((translationDerivation G X).toLinearMap ^ m) =
      (ρ.tangentMatrix R X ^ m).map (algebraMap R (coordinateAlgebra G)) *
        coordinateMatrix ρ := by
  induction m with
  | zero =>
    ext i j
    simp [Matrix.map_one]
  | succ m ih =>
    calc
      (coordinateMatrix ρ).map ((translationDerivation G X).toLinearMap ^ (m + 1)) =
          ((coordinateMatrix ρ).map
            ((translationDerivation G X).toLinearMap ^ m)).map
              (translationDerivation G X).toLinearMap := by
        ext i j
        simp only [Matrix.map_apply, pow_succ', Module.End.mul_apply]
      _ = ((ρ.tangentMatrix R X ^ m).map
            (algebraMap R (coordinateAlgebra G)) * coordinateMatrix ρ).map
              (translationDerivation G X).toLinearMap := by rw [ih]
      _ = (ρ.tangentMatrix R X ^ m).map (algebraMap R (coordinateAlgebra G)) *
          (coordinateMatrix ρ).map (translationDerivation G X).toLinearMap :=
        map_linearMap_constant_mul _ _ _
      _ = (ρ.tangentMatrix R X ^ (m + 1)).map
          (algebraMap R (coordinateAlgebra G)) * coordinateMatrix ρ := by
        change _ * (coordinateMatrix ρ).map (translationDerivation G X) = _
        rw [coordinateMatrix_translationDerivation, ← mul_assoc, ← Matrix.map_mul,
          ← pow_succ]

/-- Evaluation of any global derivation at identity computes every actual
representation differential on the resulting Lie element. -/
theorem tangentMatrix_kernelOfDerivation
    (D : Derivation R (coordinateAlgebra G) (coordinateAlgebra G)) :
    ρ.tangentMatrix R (kernelOfDerivation G D) =
      ((coordinateMatrix ρ).map D).map (coordinateOrigin G) := by
  rw [tangentMatrix_eq_coordinateMatrix]
  ext i j
  exact pointCoordinates_kernelOfDerivation_snd G D (coordinateMatrix ρ i j)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- An actual Lie-kernel point obtained by evaluating the prime-power
iterate of the translation derivation at identity. -/
def primePowerKernel (X : lieKernel G R) (p r : ℕ) [Fact p.Prime] [CharP R p] :
    lieKernel G R :=
  kernelOfDerivation G
    (Langlands.Algebra.DerivationPower.primePower (translationDerivation G X) p r)

@[simp] theorem primePowerKernel_zero
    (X : lieKernel G R) (p : ℕ) [Fact p.Prime] [CharP R p] :
    primePowerKernel G X p 0 = X := by
  simp [primePowerKernel]

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.MatrixRepresentation

open Lie

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {n : ℕ}

/-- Every actual representation sends the constructed prime-power Lie element
to the same power of its actual tangent matrix. -/
theorem tangentMatrix_primePowerKernel (ρ : MatrixRepresentation G (Fin n))
    (X : lieKernel G R) (p r : ℕ) [Fact p.Prime] [CharP R p] :
    ρ.tangentMatrix R (primePowerKernel G X p r) =
      ρ.tangentMatrix R X ^ (p ^ r) := by
  rw [primePowerKernel, tangentMatrix_kernelOfDerivation]
  change ((coordinateMatrix ρ).map
    ((translationDerivation G X).toLinearMap ^ (p ^ r))).map (coordinateOrigin G) = _
  rw [coordinateMatrix_translationDerivation_pow, Matrix.map_mul,
    coordinateMatrix_origin, mul_one]
  ext i j
  exact (coordinateOrigin G).commutes _

end Langlands.GroupScheme.MatrixRepresentation
