import Langlands.AlgebraicGeometry.PointManifold.General.RegularCharts
import Langlands.AlgebraicGeometry.PointManifold.RegularChartExistence

/-! # Universe-general algebraic smoothness to actual regular charts: exact target -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

/-- Only algebraic constant relative dimension is supplied as the chart-existence input. -/
def regularChartExistenceStatement (k : Type u) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) : Prop :=
  SmoothOfRelativeDimension d X.hom → Nonempty (RegularAtlas k X d)

/-- At Type 0 this target is equivalent to the published chart-existence obligation. -/
theorem regularChartExistenceStatement_typeZero_iff (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularChartExistenceStatement k X d ↔ PointManifold.regularChartExistenceStatement k X d := by
  constructor
  · intro h hs
    obtain ⟨A⟩ := h hs
    exact ⟨RegularAtlas.typeZeroEquiv.symm A⟩
  · intro h hs
    obtain ⟨A⟩ := h hs
    exact ⟨RegularAtlas.typeZeroEquiv A⟩

end Langlands.AlgebraicGeometry.PointManifold.General
