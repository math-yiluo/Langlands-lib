import Langlands.AlgebraicGeometry.PointManifold.General.StandardSmoothRegularCharts
import Langlands.AlgebraicGeometry.PointManifold.General.StandardSmoothReduction

/-! # Universe-general Existence of regular charts on actual smooth affine points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold.General

/-- Algebraic smoothness of constant relative dimension supplies a regular atlas
on the actual affine real or complex point topology. -/
theorem regularChartExistence (k : Type u) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularChartExistenceStatement k X d :=
  regularChartExistence_of_standardSmooth k X d
    (fun _ _ h q => exists_regularChart_of_standardSmooth h q)

end Langlands.AlgebraicGeometry.PointManifold.General
