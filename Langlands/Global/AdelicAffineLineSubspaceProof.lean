import Langlands.Global.AdelicAffineLineSubspaceStatement
import Langlands.Global.AdelicProjectiveComparisonProof

/-! # The projective affine-line subspace topology is the full-product topology -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Products of the local standard affine charts identify the adelic affine
subspace topology over a global function field. -/
theorem curvePlaceAffineLineSubspace : CurvePlaceAffineLineSubspaceStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S
  let Y := projectivePointScheme F 1
  let := curvePlaceProductSubspaceAdeleTopology k F
  let := curvePlaceProjectiveAdelePointTopology k F S 1
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  have hcoeff : IsEmbedding (curvePlaceCompletionProductMap k F) :=
    (curvePlaceCompletionProductMap_injective k F).isEmbedding_induced
  have hpi : IsEmbedding (Pi.map (fun v : AlgebraicCurve.Place k F =>
      projectiveLineAffinePoint F (curvePlaceCompletion v))) :=
    IsEmbedding.piMap (fun v => (isOpenEmbedding_projectiveLineAffinePoint F
      (curvePlaceCompletion v)).isEmbedding)
  have heq : curvePlaceAdelePointMap k F Y ∘
      projectiveLineAffinePoint F (CurvePlaceAdeleRing k F) =
      Pi.map (fun v : AlgebraicCurve.Place k F =>
        projectiveLineAffinePoint F (curvePlaceCompletion v)) ∘
        curvePlaceCompletionProductMap k F := by
    funext a v
    exact projectiveLineAffinePoint_changeRing F (CurvePlaceAdeleRing k F)
      (curvePlaceCompletion v) (curvePlaceAdeleProjection k F v) a
  have hcomp := hpi.comp hcoeff
  rw [← heq] at hcomp
  exact ((curvePlaceProjectiveComparison k F S 1).1.isEmbedding.of_comp_iff).mp hcomp

/-- The same argument retains both infinite and finite families over a number field. -/
theorem numberFieldAffineLineSubspace : NumberFieldAffineLineSubspaceStatement.{u} := by
  intro K _ _ S
  let Y := projectivePointScheme K 1
  let := numberFieldProductSubspaceAdeleTopology K
  let := numberFieldProjectiveAdelePointTopology K S 1
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  have hcoeff : IsEmbedding (numberFieldCompletionProductMap K) :=
    (numberFieldCompletionProductMap_injective K).isEmbedding_induced
  have hinf := IsEmbedding.piMap (fun v : InfinitePlace K =>
    (isOpenEmbedding_projectiveLineAffinePoint K (InfiniteCompletion K v)).isEmbedding)
  have hfin := IsEmbedding.piMap (fun v : FinitePlace K =>
    (isOpenEmbedding_projectiveLineAffinePoint K (FiniteCompletion K v)).isEmbedding)
  have hprod := hinf.prodMap hfin
  have heq : numberFieldAdelePointMap K Y ∘ projectiveLineAffinePoint K (Adeles K) =
      Prod.map (Pi.map (fun v : InfinitePlace K =>
        projectiveLineAffinePoint K (InfiniteCompletion K v)))
        (Pi.map (fun v : FinitePlace K => projectiveLineAffinePoint K (FiniteCompletion K v))) ∘
          numberFieldCompletionProductMap K := by
    funext a
    apply Prod.ext
    · funext v
      exact projectiveLineAffinePoint_changeRing K (Adeles K) (InfiniteCompletion K v)
        (numberFieldInfiniteAdeleProjection K v) a
    · funext v
      exact projectiveLineAffinePoint_changeRing K (Adeles K) (FiniteCompletion K v)
        (numberFieldFiniteAdeleProjection K v) a
  have hcomp := hprod.comp hcoeff
  rw [← heq] at hcomp
  exact ((numberFieldProjectiveComparison K S 1).1.isEmbedding.of_comp_iff).mp hcomp

/-- The original affine-line adelic subspace has exactly the full-product topology. -/
theorem adelicAffineLineSubspace : AdelicAffineLineSubspaceStatement.{u} :=
  ⟨curvePlaceAffineLineSubspace, numberFieldAffineLineSubspace⟩

end Langlands.Global
