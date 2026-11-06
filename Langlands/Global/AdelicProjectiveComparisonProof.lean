import Langlands.Global.AdelicProjectiveComparisonStatement
import Langlands.Global.AdelicProperAllPlaceProof

/-! # The concrete projective specialization of proper adelic points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The canonical projective model satisfies the concrete function-field target. -/
theorem curvePlaceProjectiveComparison : CurvePlaceProjectiveComparisonStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S n
  let X := curvePlaceProjectiveModel k F S n
  let Y := projectivePointScheme F n
  let e := curvePlaceProjectiveGenericFiberIso k F S n
  let := curvePlaceProjectiveAdelePointTopology k F S n
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let (v : AlgebraicCurve.Place k F) : T2Space (RingPoint F Y (curvePlaceCompletion v)) :=
    t2Space_schemePointTopology F (curvePlaceCompletion v) Y
  have h := curvePlaceProperAllPlace k F S X Y e
  exact ⟨h, curvePlaceSpreadCompactness k F S X Y e, h.homeomorph.symm.t2Space⟩

/-- The canonical full number-field projective model retains all local factors. -/
theorem numberFieldProjectiveComparison : NumberFieldProjectiveComparisonStatement.{u} := by
  intro K _ _ S n
  let X := numberFieldProjectiveModel K S n
  let Y := projectivePointScheme K n
  let e := numberFieldProjectiveGenericFiberIso K S n
  let := numberFieldProjectiveAdelePointTopology K S n
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let (v : InfinitePlace K) : T2Space (RingPoint K Y (InfiniteCompletion K v)) :=
    t2Space_schemePointTopology K (InfiniteCompletion K v) Y
  let (v : FinitePlace K) : T2Space (RingPoint K Y (FiniteCompletion K v)) :=
    t2Space_schemePointTopology K (FiniteCompletion K v) Y
  have h := numberFieldProperAllPlace K S X Y e
  exact ⟨h, numberFieldSpreadCompactness K S X Y e, h.homeomorph.symm.t2Space⟩

/-- The full-product compact-Hausdorff assertion for actual projective adelic points. -/
theorem adelicProjectiveComparison : AdelicProjectiveComparisonStatement.{u} :=
  ⟨curvePlaceProjectiveComparison, numberFieldProjectiveComparison⟩

end Langlands.Global
