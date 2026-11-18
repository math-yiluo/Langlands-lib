import Langlands.GroupScheme.OddOrthogonalMatrix.ReducedTriviality

/-! # Exact all-test matrix image of the odd norm-one group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- The all-test matrix chart is injective. -/
theorem pointMatrix_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (pointMatrix (l := l) K T) := by
  intro x y h
  apply (cancel_mono (inclusion K).hom.hom).mp
  apply (GeneralLinear.pointsEquiv (Index l) (CommRingCat.of K) T).injective
  rwa [pointsEquiv_inclusion, pointsEquiv_inclusion]

/-- The full all-test matrix image is exactly the determinant-one quadratic
isometry equations, including for nonaffine and nonreduced tests. -/
theorem mem_range_pointMatrix_iff (T : Over (Spec (CommRingCat.of K)))
    (g : GL (Index l) Γ(T.left, ⊤)) :
    g ∈ (pointMatrix K T).range ↔
      OrthogonalMatrix.IsAlt (g.val * (formMatrix l K).map (scalarMap T) * g.val.transpose -
        (formMatrix l K).map (scalarMap T)) ∧ g.val.det = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact pointMatrix_equations K T z
  · intro hg
    let a := (FiniteAlgebraUnits.pointsEquiv
      (Module.finBasis K (Matrix (Index l) (Index l) K)) T).symm
        (Units.mapEquiv (matrixEquiv (n := Index l) K
          ((algΓ (CommRingCat.of K)).obj T).unop).symm.toMulEquiv g)
    have ha : ambientMatrix K T a = g.val := by
      unfold ambientMatrix a
      rw [MulEquiv.apply_symm_apply]
      exact (matrixEquiv (n := Index l) K _).apply_symm_apply _
    have hamem : a ∈ (SubgroupFunctor.range
        ((scalar K).normOneIsometryAmbientι (form l K))).carrier T := by
      rw [mem_range_normOneIsometryAmbientι_iff K (form l K) (formMatrix l K) rfl]
      change OrthogonalMatrix.IsAlt (ambientMatrix K T a *
        (formMatrix l K).map (algebraMap K ((algΓ (CommRingCat.of K)).obj T).unop) *
          (ambientMatrix K T a).transpose -
            (formMatrix l K).map (algebraMap K ((algΓ (CommRingCat.of K)).obj T).unop)) ∧
              (ambientMatrix K T a).det = 1
      rwa [ha]
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hamem
    refine ⟨z, ?_⟩
    apply Units.ext
    rw [pointMatrix_val, hz, ha]

/-- Actual points identify multiplicatively with their full matrix image. -/
def pointMatrixRangeEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme l K).X) ≃* (pointMatrix (l := l) K T).range :=
  MulEquiv.ofBijective (pointMatrix K T).rangeRestrict
    ⟨fun _x _y h => pointMatrix_injective (l := l) K T (congrArg Subtype.val h),
      (pointMatrix K T).rangeRestrict_surjective⟩

@[simp] theorem pointMatrixRangeEquiv_val (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (groupScheme l K).X) :
    (pointMatrixRangeEquiv K T x).val = pointMatrix K T x := rfl

/-- Reconstructing an admissible matrix recovers precisely that matrix. -/
theorem pointMatrix_pointMatrixRangeEquiv_symm (T : Over (Spec (CommRingCat.of K)))
    (g : (pointMatrix (l := l) K T).range) :
    pointMatrix K T ((pointMatrixRangeEquiv K T).symm g) = g.val :=
  congrArg Subtype.val ((pointMatrixRangeEquiv K T).apply_symm_apply g)

end Langlands.GroupScheme.OddOrthogonalMatrix
