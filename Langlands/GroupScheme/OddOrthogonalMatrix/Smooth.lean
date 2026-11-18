import Langlands.GroupScheme.OddOrthogonalMatrix.TangentChart
import Langlands.GroupScheme.Lie.SmoothSourceChart

/-! # Smoothness of the actual odd norm-one isometry group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- The actual smooth source, identity-preserving ordered chart and
surjective identity tangent lifts for the split odd norm-one group. -/
def smoothSourceChart : LieKernelSurjectiveChart (groupScheme l K) where
  source := tangentChartSource (l := l) K
  smoothSource := inferInstance
  chart := tangentChart K
  one_chart _ := one_comp_tangentChart K
  tangent_surjective := tangentChart_lieKernel_surjective K

/-- The actual norm-one group of the standard odd radical-free quadratic
form is smooth over every field, including imperfect characteristic two. -/
instance smooth_groupScheme : Smooth (groupScheme l K).X.hom :=
  smooth_of_lieKernel_surjective_chart (tangentChart K)
    (fun _ => one_comp_tangentChart K) (tangentChart_lieKernel_surjective K)

end Langlands.GroupScheme.OddOrthogonalMatrix
