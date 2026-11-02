import Langlands.GroupScheme.AffinePointRegularLieGroup
import Langlands.AlgebraicGeometry.PointManifold.RegularChartExistenceProof
import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparisonProof

/-! # The actual smooth affine point Lie group and family criterion -/

noncomputable section

universe v w

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointManifold

/-- Algebraic smoothness gives one regular atlas with both the original point
Lie group structure and the coordinate-smooth family criterion. -/
theorem smoothAffineGroupManifold (k : Type) [RCLike k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] (d : ℕ) :
    smoothAffineGroupManifoldStatement.{v, w} (k := k) G (d := d) := by
  intro hsmooth
  obtain ⟨A⟩ := regularChartExistence k G.X d hsmooth
  refine ⟨A, ?_⟩
  let := A.chartedSpace
  refine ⟨regularAtlasLieGroup G A (regularAtlasComparison.{0, 0, 0} k G.X d), ?_⟩
  intro E _ _ H _ I M _ _ _ p
  exact regularAtlas_contMDiff_iff_coordinateSmooth G I A
    (regularAtlasComparison.{v, v, w} k G.X d).2 p

/-- The real specialization, with real model dimension `d`. -/
theorem realSmoothAffineGroupManifold
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ) :
    realSmoothAffineGroupManifoldStatement.{v, w} G d :=
  smoothAffineGroupManifold.{v, w} ℝ G d

/-- The complex specialization, with real model dimension `2 * d`. -/
theorem complexSmoothAffineGroupManifold
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ) :
    complexSmoothAffineGroupManifoldStatement.{v, w} G d :=
  smoothAffineGroupManifold.{v, w} ℂ G d

end Langlands.GroupScheme
