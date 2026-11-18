import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.OrthogonalMatrix.ScalarPoints

/-! # Scalar orthogonal cocycles on finite Galois covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

open Quaternionic
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [CharZero F] {n : ℕ}
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "U" => GaloisCocycle.cover F L
local notation "Lalg" => CommAlgCat.of (CommRingCat.of F) L

/-- Read a natural scalar orthogonal cocycle as a crossed cocycle of invertible matrices. -/
def scalarMatrixCocycle (ξ : Cocycle ((FirstKindInvolution.scalar F).isometryGroup q) U) :
    OrthogonalCocycle (L := L) ((FirstKindInvolution.scalar F).polar q) where
  toFun σ := scalarMatrixPoint q Lalg (GaloisCocycle.value ξ σ)
  one := by
    change scalarMatrixPoint q Lalg (ξ.toFun (𝟙 _) (GaloisCocycle.arrow F L 1)) = 1
    rw [GaloisCocycle.arrow_one, ξ.toFun_self, map_one]
  mul σ τ := by
    rw [GaloisCocycle.value_mul, map_mul]
    congr 1
    exact scalarMatrixPoint_naturality q (CommAlgCat.ofHom σ.toAlgHom) _
  preserves σ := scalarMatrixPoint_preserves q Lalg (GaloisCocycle.value ξ σ)

/-- The matrix of a twisted cocycle is obtained by the same twist of its matrices. -/
theorem scalarMatrixCocycle_twist
    (ξ : Cocycle ((FirstKindInvolution.scalar F).isometryGroup q) U)
    (f : U ⟶ ((FirstKindInvolution.scalar F).isometryGroup q).X) (σ : L ≃ₐ[F] L) :
    (scalarMatrixCocycle q (ξ.twist f)).toFun σ =
      (scalarMatrixPoint q Lalg f)⁻¹ * (scalarMatrixCocycle q ξ).toFun σ *
        Matrix.GeneralLinearGroup.map σ.toRingHom (scalarMatrixPoint q Lalg f) := by
  change scalarMatrixPoint q Lalg
      ((𝟙 U ≫ f)⁻¹ * GaloisCocycle.value ξ σ * (GaloisCocycle.arrow F L σ ≫ f)) = _
  rw [Category.id_comp, map_mul, map_mul, map_inv]
  congr 1
  exact scalarMatrixPoint_naturality q (CommAlgCat.ofHom σ.toAlgHom) f

variable [FiniteDimensional F L] [IsGalois F L]

/-- On the finite Galois cover, cohomology of matrices detects cohomology on all tests. -/
theorem cohomologous_iff_scalarMatrixCocycle
    (ξ ζ : Cocycle ((FirstKindInvolution.scalar F).isometryGroup q) U) :
    ξ.Cohomologous ζ ↔ (scalarMatrixCocycle q ξ).Cohomologous (scalarMatrixCocycle q ζ) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨scalarMatrixPoint q Lalg f, scalarMatrixPoint_preserves q Lalg f, fun σ => ?_⟩
    have h := congrArg (scalarMatrixPoint q Lalg) (hf (𝟙 U) (GaloisCocycle.arrow F L σ))
    exact h.trans (scalarMatrixCocycle_twist q ξ f σ)
  · rintro ⟨a, ha, h⟩
    obtain ⟨f, hf⟩ := exists_scalarMatrixPoint_eq q Lalg a ha
    refine ⟨f, fun x y => GaloisCocycle.toFun_eq_of_value_eq ζ (ξ.twist f) (fun σ => ?_) x y⟩
    apply scalarMatrixPoint_injective q Lalg
    change (scalarMatrixCocycle q ζ).toFun σ = (scalarMatrixCocycle q (ξ.twist f)).toFun σ
    rw [scalarMatrixCocycle_twist, hf]
    exact h σ

end Langlands.GroupScheme.OrthogonalMatrix
