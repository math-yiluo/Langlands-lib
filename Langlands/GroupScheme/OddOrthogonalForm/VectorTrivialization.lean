import Langlands.GroupScheme.OddOrthogonalForm.AutomorphismCocycle
import Langlands.LinearAlgebra.GaloisVectorDescent

/-! # A matrix basis trivialising the exact odd cocycle -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix
open Langlands.LinearAlgebra.GaloisVectorDescent

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}
variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))

/-- The inverse cocycle consists of exact norm-one quadratic isometries. -/
theorem matrixCocycle_equations (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) :
    OrthogonalMatrix.IsAlt ((matrixCocycle φ hn σ).val * formMatrix (Fin n) N *
      (matrixCocycle φ hn σ).val.transpose - formMatrix (Fin n) N) ∧
        (matrixCocycle φ hn σ).val.det = 1 := by
  have h := rationalMatrix_equations (conjugatorPoint hn (galoisTwist φ σ))⁻¹
  simpa only [matrixCocycle, galoisConjugator, conjugatorMatrix, rationalMatrix,
    _root_.map_inv] using h

variable [FiniteDimensional K N]

/-- A Hilbert-90 basis for the exact matrix cocycle. -/
def descentBasis (hn : 2 ≤ n) : GL (Index (Fin n)) N :=
  coboundaryMatrix (⊤ : Subgroup (N ≃ₐ[K] N))
    (fun σ => (matrixCocycle φ hn σ.val).val)
    (by rw [Subgroup.coe_one, matrixCocycle_one]; rfl)
    (by
      intro σ τ
      change (matrixCocycle φ hn (σ.val * τ.val)).val = _
      rw [matrixCocycle_mul]
      rfl)

/-- Its coefficients satisfy the exact Hilbert-90 equation. -/
theorem descentBasis_spec (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) :
    matrixCocycle φ hn σ * Matrix.GeneralLinearGroup.map (σ : N →+* N) (descentBasis φ hn) =
      descentBasis φ hn := by
  apply Units.ext
  exact coboundaryMatrix_spec (n := Index (Fin n)) (⊤ : Subgroup (N ≃ₐ[K] N))
    (fun τ => (matrixCocycle φ hn τ.val).val)
    (by rw [Subgroup.coe_one, matrixCocycle_one]; rfl)
    (by
      intro τ ρ
      change (matrixCocycle φ hn (τ.val * ρ.val)).val = _
      rw [matrixCocycle_mul]
      rfl) ⟨σ, Subgroup.mem_top σ⟩

/-- The original isometric conjugator is the change of the chosen basis under a field
 automorphism. -/
theorem galoisConjugator_eq_basis (hn : 2 ≤ n) (σ : N ≃ₐ[K] N) :
    galoisConjugator φ hn σ =
      Matrix.GeneralLinearGroup.map (σ : N →+* N) (descentBasis φ hn) * (descentBasis φ hn)⁻¹ := by
  have h := congrArg (fun z => galoisConjugator φ hn σ * z * (descentBasis φ hn)⁻¹)
    (descentBasis_spec φ hn σ)
  simpa only [matrixCocycle, ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right] using h.symm

end Langlands.GroupScheme.OddOrthogonalForm
