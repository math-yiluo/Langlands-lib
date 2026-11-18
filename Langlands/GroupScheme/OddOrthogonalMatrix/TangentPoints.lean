import Langlands.GroupScheme.OddOrthogonalMatrix.EvenInclusion
import Langlands.GroupScheme.OddOrthogonalMatrix.LieMatrices
import Langlands.GroupScheme.Quaternionic.NormOneIsometryAffinePoints
import Langlands.GroupScheme.SpecialLinearTorus

/-! # Actual affine tangent points of the odd norm-one group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates
open GeneralLinear.DualNumber

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- Matrix coordinates of actual affine points, including nonreduced coefficients. -/
def affineMatrix (A : CommAlgCat.{u} (CommRingCat.of K)) :
    ((algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) →*
      Matrix.GeneralLinearGroup (Index l) A :=
  (Units.mapEquiv (matrixEquiv (n := Index l) K A).toMulEquiv).toMonoidHom.comp
    (((scalar K).tensorIsometryGroup (form l K) A).subtype.comp
      (((scalar K).tensorNormOneIsometryGroup (form l K) A).subtype.comp
        ((scalar K).normOneIsometryAffinePointsEquiv (form l K) A).toMonoidHom))

/-- The actual ambient affine tensor unit gives these matrix coordinates. -/
theorem affineMatrix_val (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) :
    (affineMatrix K A z : Matrix (Index l) (Index l) A) = matrixEquiv K A
      (FiniteAlgebraUnits.affinePointsEquiv
        (Module.finBasis K (Matrix (Index l) (Index l) K)) A
          (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) :
            A ⊗[K] Matrix (Index l) (Index l) K) := by
  change matrixEquiv (n := Index l) K A
    (((scalar K).normOneIsometryAffinePointsEquiv (form l K) A z).val.val :
      A ⊗[K] Matrix (Index l) (Index l) K) = _
  rw [normOneIsometryAffinePointsEquiv_val]

/-- Actual affine norm-one points are determined by their coefficient matrices. -/
theorem affineMatrix_injective (A : CommAlgCat.{u} (CommRingCat.of K)) :
    Function.Injective (affineMatrix (l := l) K A) := by
  intro x y h
  apply ((scalar K).normOneIsometryAffinePointsEquiv (form l K) A).injective
  apply Subtype.ext
  apply Subtype.ext
  exact (Units.mapEquiv (matrixEquiv (n := Index l) K A).toMulEquiv).injective h

/-- Affine matrix coordinates commute with coefficient-algebra homomorphisms. -/
theorem affineMatrix_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) :
    affineMatrix K B ((algSpec (CommRingCat.of K)).map f.op ≫ z) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (affineMatrix K A z) := by
  apply Units.ext
  rw [affineMatrix_val]
  change matrixEquiv K B (FiniteAlgebraUnits.affinePointsEquiv
    (Module.finBasis K (Matrix (Index l) (Index l) K)) B
      (((algSpec (CommRingCat.of K)).map f.op ≫ z) ≫
        ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) : _) =
      (affineMatrix K A z : Matrix (Index l) (Index l) A).map f.hom
  rw [Category.assoc, FiniteAlgebraUnits.affinePointsEquiv_naturality]
  change matrixEquiv K B (Algebra.TensorProduct.map f.hom
    (AlgHom.id K (Matrix (Index l) (Index l) K))
      (FiniteAlgebraUnits.affinePointsEquiv
        (Module.finBasis K (Matrix (Index l) (Index l) K)) A
          (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) :
            A ⊗[K] Matrix (Index l) (Index l) K)) = _
  rw [matrixEquiv_naturality]
  exact congrArg (fun M : Matrix (Index l) (Index l) A => M.map f.hom)
    (affineMatrix_val K A z).symm

/-- Every actual affine point satisfies alternating quadratic defect and
ordinary determinant one over its original coefficient algebra. -/
theorem affineMatrix_equations (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) :
    let g : Matrix (Index l) (Index l) A := affineMatrix K A z
    OrthogonalMatrix.IsAlt (g * (formMatrix l K).map (algebraMap K A) * g.transpose -
      (formMatrix l K).map (algebraMap K A)) ∧ g.det = 1 := by
  let c := (scalar K).normOneIsometryAffinePointsEquiv (form l K) A z
  have hQ := c.val.property
  change Quaternionic.IsometryCut.defect ((scalar K).matrix (Index l))
    (Quotient.out (form l K)) (c.val.val : A ⊗[K] Matrix (Index l) (Index l) K) ∈
      ((scalar K).quadraticKernel (Index l)).baseChange A at hQ
  have hrep : Quotient.out (form l K) - formMatrix l K ∈
      (scalar K).quadraticKernel (Index l) := by
    rw [← Submodule.Quotient.eq]
    exact Submodule.Quotient.mk_out (form l K)
  have hQ' := (Quaternionic.IsometryCut.defect_mem_iff_of_sub_mem
    Quaternionic.IsometryCut.isStable_alternatingSubspace hrep _).1 hQ
  change Quaternionic.IsometryCut.defect ((scalar K).matrix (Index l)) (formMatrix l K)
    (c.val.val : A ⊗[K] Matrix (Index l) (Index l) K) ∈
      ((scalar K).quadraticKernel (Index l)).baseChange A at hQ'
  rw [mem_quadraticKernel_baseChange_iff, matrixEquiv_defect] at hQ'
  refine ⟨hQ', ?_⟩
  have hN := congrArg Units.val c.property
  change CentralSimple.reducedNorm K (Matrix (Index l) (Index l) K) A
    (c.val.val : A ⊗[K] Matrix (Index l) (Index l) K) = 1 at hN
  rw [reducedNorm_eq_det] at hN
  exact hN

variable {K}

/-- The square-zero linearization of the odd quadratic defect. -/
theorem defect_one_add_epsilonMatrix (Y : Matrix (Index l) (Index l) K) :
    (1 + epsilonMatrix Y) * (formMatrix l K).map (algebraMap K (DualNumber K)) *
        (1 + epsilonMatrix Y).transpose - (formMatrix l K).map (algebraMap K (DualNumber K)) =
      epsilonMatrix (lieDefect Y) := by
  have hT : (epsilonMatrix Y).transpose = epsilonMatrix Y.transpose := rfl
  change (1 + epsilonMatrix Y) * (formMatrix l K).map (TrivSqZeroExt.inlHom K K) *
    (1 + epsilonMatrix Y).transpose - (formMatrix l K).map (TrivSqZeroExt.inlHom K K) = _
  rw [Matrix.transpose_add, Matrix.transpose_one, hT]
  simp only [add_mul, mul_add, one_mul, mul_one, epsilonMatrix_mul_constantMatrix,
    constantMatrix_mul_epsilonMatrix, epsilonMatrix_mul, add_zero, lieDefect,
    LinearMap.coe_mk, AddHom.coe_mk, epsilonMatrix_add]
  abel

omit [Fintype l] [DecidableEq l] in
/-- Alternation of an epsilon matrix is equivalent to alternation of its
coefficient matrix. -/
theorem isAlt_epsilonMatrix_iff (M : Matrix (Index l) (Index l) K) :
    OrthogonalMatrix.IsAlt (epsilonMatrix M) ↔ OrthogonalMatrix.IsAlt M := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V.map TrivSqZeroExt.snd, ?_⟩
    ext i j
    have h := congrArg (fun N : Matrix (Index l) (Index l) (DualNumber K) =>
      TrivSqZeroExt.snd (N i j)) hV
    simpa using h
  · rintro ⟨U, rfl⟩
    refine ⟨epsilonMatrix U, ?_⟩
    apply Matrix.ext
    intro i j
    change (TrivSqZeroExt.inr (U i j - U j i) : DualNumber K) =
      TrivSqZeroExt.inr (U i j) - TrivSqZeroExt.inr (U j i)
    exact TrivSqZeroExt.inr_sub K _ _

/-- The actual coefficient-ring equations on `1+εY` are exactly the previously
constructed linearized subspace. -/
theorem one_add_epsilonMatrix_equations_iff (Y : Matrix (Index l) (Index l) K) :
    (OrthogonalMatrix.IsAlt ((1 + epsilonMatrix Y) *
        (formMatrix l K).map (algebraMap K (DualNumber K)) *
        (1 + epsilonMatrix Y).transpose - (formMatrix l K).map (algebraMap K (DualNumber K))) ∧
      (1 + epsilonMatrix Y).det = 1) ↔ Y ∈ lieMatrices := by
  rw [defect_one_add_epsilonMatrix, isAlt_epsilonMatrix_iff,
    SpecialLinear.one_add_epsilonMatrix_det_eq_one_iff, mem_lieMatrices_iff]

variable (K)

local notation "𝔻" => CommAlgCat.of (CommRingCat.of K) (DualNumber K)

/-- A solution of the linearized equations gives an actual norm-one tensor
isometry over the dual numbers. -/
def tangentTensorUnit (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (scalar K).tensorNormOneIsometryGroup (form l K) (DualNumber K) := by
  let w := Units.mapEquiv (matrixEquiv (n := Index l) K (DualNumber K)).symm.toMulEquiv (matrixUnit Y)
  have hw : matrixEquiv K (DualNumber K)
      (w : DualNumber K ⊗[K] Matrix (Index l) (Index l) K) = 1 + epsilonMatrix Y :=
    (matrixEquiv K (DualNumber K)).apply_symm_apply _
  have hQ := ((one_add_epsilonMatrix_equations_iff Y).2 hY).1
  have hN := ((one_add_epsilonMatrix_equations_iff Y).2 hY).2
  have hdef : Quaternionic.IsometryCut.defect ((scalar K).matrix (Index l)) (formMatrix l K)
      (w : DualNumber K ⊗[K] Matrix (Index l) (Index l) K) ∈
        ((scalar K).quadraticKernel (Index l)).baseChange (DualNumber K) := by
    rw [mem_quadraticKernel_baseChange_iff, matrixEquiv_defect, hw]
    exact hQ
  have hrep : Quotient.out (form l K) - formMatrix l K ∈
      (scalar K).quadraticKernel (Index l) := by
    rw [← Submodule.Quotient.eq]
    exact Submodule.Quotient.mk_out (form l K)
  refine ⟨⟨w, (Quaternionic.IsometryCut.defect_mem_iff_of_sub_mem
    Quaternionic.IsometryCut.isStable_alternatingSubspace hrep _).2 hdef⟩, ?_⟩
  apply Units.ext
  change CentralSimple.reducedNorm K (Matrix (Index l) (Index l) K) (DualNumber K) (w : _) = 1
  rw [reducedNorm_eq_det, hw]
  exact hN

/-- The underlying tensor unit in the tangent construction is the inverse-chart
image of the standard dual-number matrix. -/
theorem tangentTensorUnit_val (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (tangentTensorUnit K Y hY).val.val =
      Units.mapEquiv (matrixEquiv (n := Index l) K (DualNumber K)).symm.toMulEquiv
        (matrixUnit Y) := rfl

/-- An actual affine dual-number point of the odd norm-one group for every
solution of the linearized equations. -/
def tangentPoint (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).obj (op 𝔻) ⟶ (groupScheme l K).X :=
  ((scalar K).normOneIsometryAffinePointsEquiv (form l K) 𝔻).symm (tangentTensorUnit K Y hY)

set_option maxHeartbeats 800000 in
/-- The constructed actual dual-number point has coefficient matrix `1+εY`. -/
theorem affineMatrix_tangentPoint (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    affineMatrix K 𝔻 (tangentPoint K Y hY) = matrixUnit Y := by
  calc
    _ = Units.mapEquiv (matrixEquiv (n := Index l) K (DualNumber K)).toMulEquiv
        (tangentTensorUnit K Y hY).val.val := by
      exact congrArg (fun c : (scalar K).tensorNormOneIsometryGroup (form l K) (DualNumber K) =>
        Units.mapEquiv (matrixEquiv (n := Index l) K (DualNumber K)).toMulEquiv c.val.val)
          (((scalar K).normOneIsometryAffinePointsEquiv (form l K) 𝔻).apply_symm_apply
            (tangentTensorUnit K Y hY))
    _ = matrixUnit Y := by
      rw [tangentTensorUnit_val]
      apply Units.ext
      change matrixEquiv (n := Index l) K (DualNumber K)
        ((matrixEquiv (n := Index l) K (DualNumber K)).symm _) = _
      exact (matrixEquiv K (DualNumber K)).apply_symm_apply _

/-- The actual dual-number point reduces to the identity, with no smoothness
assumption on the odd group. -/
theorem tangentPoint_reduction (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K)).op ≫ tangentPoint K Y hY = 1 := by
  apply affineMatrix_injective K (CommAlgCat.of (CommRingCat.of K) K)
  rw [affineMatrix_naturality, affineMatrix_tangentPoint, _root_.map_one]
  exact matrixReduction_matrixUnit Y

end Langlands.GroupScheme.OddOrthogonalMatrix
