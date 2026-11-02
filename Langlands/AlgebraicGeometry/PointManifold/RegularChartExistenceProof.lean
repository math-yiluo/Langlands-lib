import Langlands.AlgebraicGeometry.PointManifold.StandardSmoothRegularCharts
import Langlands.AlgebraicGeometry.PointManifold.StandardSmoothReduction

/-! # Existence of regular charts on actual smooth affine points -/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold

/-- Algebraic smoothness of constant relative dimension supplies a regular atlas
on the actual affine real or complex point topology. -/
theorem regularChartExistence (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularChartExistenceStatement k X d :=
  regularChartExistence_of_standardSmooth k X d
    (fun _ _ h q => exists_regularChart_of_standardSmooth h q)

end Langlands.AlgebraicGeometry.PointManifold
