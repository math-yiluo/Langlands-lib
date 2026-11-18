import Langlands.GroupScheme.OrthogonalMatrix.Comparison
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaAffine
import Langlands.LinearAlgebra.OrthogonalCocycleComparison

/-! # Polar matrices of scalar orthogonal group points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.OrthogonalMatrix

open Quaternionic
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {F : Type u} [Field F] {n : ℕ}

/-- The polar matrix of a scalar quadratic form is symmetric. -/
theorem scalar_polar_transpose (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)) :
    ((FirstKindInvolution.scalar F).polar q)ᵀ = (FirstKindInvolution.scalar F).polar q := by
  rw [← Submodule.Quotient.mk_out q, FirstKindInvolution.polar_mk,
    FirstKindInvolution.scalar_matrix_apply, Matrix.transpose_add, Matrix.transpose_transpose,
    add_comm]

private theorem isAlt_iff_polar {R : Type*} [CommRing R] (h₂ : IsUnit (2 : R))
    (Q : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) :
    IsAlt (gramTransform g Q - Q) ↔ gramTransform g (Q + Qᵀ) = Q + Qᵀ := by
  let D := gramTransform g Q - Q
  have hD : D + Dᵀ = gramTransform g (Q + Qᵀ) - (Q + Qᵀ) := by
    simp only [D, gramTransform, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  change IsAlt D ↔ _
  conv_rhs => rw [← sub_eq_zero, ← hD]
  rw [isAlt_iff]
  refine ⟨And.left, fun h => ⟨h, fun i => ?_⟩⟩
  apply h₂.mul_left_cancel (c := 0)
  rw [mul_zero, two_mul]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) R => M i i) h

variable (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))
  (R : CommAlgCat.{u} (CommRingCat.of F))

/-- A scalar isometry point written as a unit of the coefficient matrix ring. -/
def scalarMatrixPoint :
    ((FirstKindInvolution.scalar F).isometryGroup q).affinePoints R →* GL (Fin n) R :=
  (Units.map (chart F (Fin n) R).toMonoidHom).comp
    (((FirstKindInvolution.scalar F).isometryUnits (Quotient.out q) R).subtype.comp
      (OrthogonalMorita.isometryAffineUnitsEquiv (FirstKindInvolution.scalar F) q R).toMonoidHom)

private theorem isometryUnits_iff_polar [CharZero F] (y : (R ⊗[F] Matrix (Fin n) (Fin n) F)ˣ) :
    y ∈ (FirstKindInvolution.scalar F).isometryUnits (Quotient.out q) R ↔
      gramTransform (Units.map (chart F (Fin n) R).toMonoidHom y)
          (((FirstKindInvolution.scalar F).polar q).map (algebraMap F R)) =
        ((FirstKindInvolution.scalar F).polar q).map (algebraMap F R) := by
  rw [IsometryCut.mem_isometrySubgroup, mem_quadraticKernel_baseChange_iff, chart_defect]
  have hQ : (FirstKindInvolution.scalar F).polar q =
      (Quotient.out q : Matrix (Fin n) (Fin n) F) + (Quotient.out q)ᵀ := by
    calc
      _ = (FirstKindInvolution.scalar F).polar (Submodule.Quotient.mk (Quotient.out q)) := by
        rw [Submodule.Quotient.mk_out]
      _ = _ := by rw [FirstKindInvolution.polar_mk, FirstKindInvolution.scalar_matrix_apply]
  rw [hQ, Matrix.map_add _ (map_add (algebraMap F R)), Matrix.transpose_map]
  have h₂ : IsUnit (2 : R) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map
      (algebraMap F R)
  exact isAlt_iff_polar h₂ ((Quotient.out q : Matrix (Fin n) (Fin n) F).map (algebraMap F R))
    (Units.map (chart F (Fin n) R).toMonoidHom y)

/-- Every coefficient point preserves the scalar extension of the polar matrix. -/
theorem scalarMatrixPoint_preserves [CharZero F]
    (a : ((FirstKindInvolution.scalar F).isometryGroup q).affinePoints R) :
    gramTransform (scalarMatrixPoint q R a)
        (((FirstKindInvolution.scalar F).polar q).map (algebraMap F R)) =
      ((FirstKindInvolution.scalar F).polar q).map (algebraMap F R) :=
  (isometryUnits_iff_polar q R _).mp
    (OrthogonalMorita.isometryAffineUnitsEquiv (FirstKindInvolution.scalar F) q R a).property

/-- The underlying matrix determines the original coefficient point. -/
theorem scalarMatrixPoint_injective : Function.Injective (scalarMatrixPoint q R) := by
  intro a b h
  apply (OrthogonalMorita.isometryAffineUnitsEquiv (FirstKindInvolution.scalar F) q R).injective
  apply Subtype.ext
  apply Units.ext
  apply (chart F (Fin n) R).injective
  exact congrArg Units.val h

/-- Every invertible coefficient matrix preserving the polar form lifts to an actual point. -/
theorem exists_scalarMatrixPoint_eq [CharZero F] (g : GL (Fin n) R)
    (hg : gramTransform g (((FirstKindInvolution.scalar F).polar q).map (algebraMap F R)) =
      ((FirstKindInvolution.scalar F).polar q).map (algebraMap F R)) :
    ∃ a : ((FirstKindInvolution.scalar F).isometryGroup q).affinePoints R,
      scalarMatrixPoint q R a = g := by
  let y := Units.map (chart F (Fin n) R).symm.toMonoidHom g
  have hy : Units.map (chart F (Fin n) R).toMonoidHom y = g := by
    apply Units.ext
    exact (chart F (Fin n) R).apply_symm_apply _
  let a := OrthogonalMorita.isometryAffineUnitsEquiv (FirstKindInvolution.scalar F) q R
  have hmem : y ∈ (FirstKindInvolution.scalar F).isometryUnits (Quotient.out q) R :=
    (isometryUnits_iff_polar q R y).mpr (hy ▸ hg)
  refine ⟨a.symm ⟨y, hmem⟩, ?_⟩
  change Units.map (chart F (Fin n) R).toMonoidHom (a (a.symm ⟨y, hmem⟩)).val = g
  rw [MulEquiv.apply_symm_apply]
  exact hy

variable {R} in
/-- The scalar matrix chart commutes with every homomorphism of coefficient algebras. -/
theorem scalarMatrixPoint_naturality {S : CommAlgCat.{u} (CommRingCat.of F)} (f : R ⟶ S)
    (a : ((FirstKindInvolution.scalar F).isometryGroup q).affinePoints R) :
    scalarMatrixPoint q S (((FirstKindInvolution.scalar F).isometryGroup q).affinePointMap f a) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (scalarMatrixPoint q R a) := by
  apply Units.ext
  change chart F (Fin n) S
      ((OrthogonalMorita.isometryAffineUnitsEquiv (FirstKindInvolution.scalar F) q S
        (((FirstKindInvolution.scalar F).isometryGroup q).affinePointMap f a)).val :
        S ⊗[F] Matrix (Fin n) (Fin n) F) = _
  rw [OrthogonalMorita.isometryAffineUnitsEquiv_naturality, IsometryCut.coe_isometrySubgroupMap]
  exact chart_naturality f.hom _

end Langlands.GroupScheme.OrthogonalMatrix
