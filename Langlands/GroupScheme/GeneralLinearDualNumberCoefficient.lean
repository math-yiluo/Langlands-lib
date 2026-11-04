import Langlands.GroupScheme.MatrixRepresentationDifferentialConjugation
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Epsilon coefficients of matrices over arbitrary dual-number rings -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {A : Type u} [CommRing A] {n : Type v}

/-- Entrywise extraction of the epsilon coefficient, at arbitrary universes. -/
def epsilonCoefficient : Matrix n n (DualNumber A) →ₗ[A] Matrix n n A where
  toFun M := Matrix.of fun i j => (M i j).snd
  map_add' M N := by
    ext i j
    exact TrivSqZeroExt.snd_add _ _
  map_smul' c M := by
    ext i j
    change (c • M i j).snd = c • (M i j).snd
    exact TrivSqZeroExt.snd_smul c (M i j)

@[simp] theorem epsilonCoefficient_apply (M : Matrix n n (DualNumber A)) (i j : n) :
    epsilonCoefficient M i j = (M i j).snd := rfl

@[simp] theorem epsilonCoefficient_epsilonMatrix (M : Matrix n n A) :
    epsilonCoefficient (epsilonMatrix M) = M := rfl

variable [Fintype n]

/-- A single epsilon factor between constant factors recovers the ordered product. -/
theorem epsilonCoefficient_constant_sandwich (L M N : Matrix n n A) :
    epsilonCoefficient
      (L.map (TrivSqZeroExt.inlHom A A) * epsilonMatrix M *
        N.map (TrivSqZeroExt.inlHom A A)) = L * M * N := by
  rw [constantMatrix_mul_epsilonMatrix, epsilonMatrix_mul_constantMatrix,
    epsilonCoefficient_epsilonMatrix]

end Langlands.GroupScheme.GeneralLinear.DualNumber
