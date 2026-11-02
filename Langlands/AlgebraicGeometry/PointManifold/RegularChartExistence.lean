import Langlands.AlgebraicGeometry.PointManifold.RegularCharts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Complex.Basic

/-! # Algebraic smoothness to regular local charts: exact target -/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

/-- The algebraic-to-analytic chart-existence obligation.
Its only smoothness input is the algebraic constant-relative-dimension property. -/
def regularChartExistenceStatement (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) : Prop :=
  SmoothOfRelativeDimension d X.hom → Nonempty (RegularAtlas k X d)

/-- The actual real-field specialization, including zero dimension and empty points. -/
abbrev realRegularChartExistenceStatement
    (X : Over (Spec (CommRingCat.of ℝ))) [IsAffine X.left] (d : ℕ) : Prop :=
  regularChartExistenceStatement ℝ X d

/-- The actual complex-field specialization; the chart model is viewed over the reals. -/
abbrev complexRegularChartExistenceStatement
    (X : Over (Spec (CommRingCat.of ℂ))) [IsAffine X.left] (d : ℕ) : Prop :=
  regularChartExistenceStatement ℂ X d

end Langlands.AlgebraicGeometry.PointManifold
