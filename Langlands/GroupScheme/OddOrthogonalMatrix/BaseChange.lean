import Langlands.GroupScheme.OddOrthogonalMatrix.MatrixPointRange

/-! # Actual change of field for the split odd norm-one model -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]
  {K L : Type u} [Field K] [Field L]

omit [Fintype l] in
/-- All coefficients of the split form are integral zeros and ones, so its
matrix over any common coefficient ring is independent of the field model. -/
theorem formMatrix_map_compare {R : Type*} [CommRing R] (f : K →+* R) (g : L →+* R) :
    (formMatrix l K).map f = (formMatrix l L).map g := by
  simp [formMatrix, OrthogonalMatrix.formMatrix, Matrix.fromBlocks_map]

variable (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))

/-- The old and new field models have identical matrix image subgroups on
the same underlying relative test scheme. -/
theorem pointMatrix_range_baseChange (T : Over (Spec (CommRingCat.of L))) :
    (pointMatrix (l := l) K ((Over.map b).obj T)).range = (pointMatrix L T).range := by
  ext g
  rw [mem_range_pointMatrix_iff, mem_range_pointMatrix_iff,
    formMatrix_map_compare (scalarMap ((Over.map b).obj T)) (scalarMap T)]
  rfl

/-- Actual base-changed points compare multiplicatively with the model over
the new field, using the full all-test matrix equations. -/
def baseChangeModelPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l K)).X) ≃*
      (T ⟶ (groupScheme l L).X) :=
  ((baseChangePointsEquiv b (groupScheme l K) T).trans
    (pointMatrixRangeEquiv K ((Over.map b).obj T))).trans
      ((MulEquiv.subgroupCongr (pointMatrix_range_baseChange (l := l) b T)).trans
        (pointMatrixRangeEquiv L T).symm)

/-- The field comparison preserves every matrix coefficient on every test. -/
theorem pointMatrix_baseChangeModelPointsEquiv (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l K)).X) :
    pointMatrix L T (baseChangeModelPointsEquiv b T x) =
      pointMatrix K ((Over.map b).obj T) (baseChangePointsEquiv b _ T x) := by
  simp only [baseChangeModelPointsEquiv, MulEquiv.trans_apply]
  exact pointMatrix_pointMatrixRangeEquiv_symm L T _

/-- The all-test comparison commutes with arbitrary test-scheme pullback. -/
theorem baseChangeModelPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l K)).X) :
    baseChangeModelPointsEquiv b T' (a ≫ x) = a ≫ baseChangeModelPointsEquiv b T x := by
  apply pointMatrix_injective L T'
  simp only [pointMatrix_baseChangeModelPointsEquiv, pointMatrix_naturality,
    baseChangePointsEquiv_naturality]
  rfl

/-- The actual split odd norm-one model commutes with change of field. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (groupScheme l K) ≅ groupScheme l L :=
  isoOfPoints (baseChangeModelPointsEquiv b) (baseChangeModelPointsEquiv_naturality b)

/-- The actual model isomorphism preserves all-test matrix coefficients. -/
theorem pointMatrix_baseChangeModelIso_hom (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme l K)).X) :
    pointMatrix L T (x ≫ (baseChangeModelIso (l := l) b).hom.hom.hom) =
      pointMatrix K ((Over.map b).obj T) (baseChangePointsEquiv b _ T x) := by
  rw [baseChangeModelIso, comp_isoOfPoints_hom, pointMatrix_baseChangeModelPointsEquiv]

end Langlands.GroupScheme.OddOrthogonalMatrix
