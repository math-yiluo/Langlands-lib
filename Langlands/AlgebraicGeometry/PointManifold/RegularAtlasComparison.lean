import Langlands.AlgebraicGeometry.PointManifold.RegularCharts
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Regular-atlas assembly and the intrinsic family criterion: exact targets -/

noncomputable section

universe v w z

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable (k : Type) [RCLike k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

/-- Smooth chart compatibility for every covering regular atlas. -/
def regularAtlasManifoldStatement : Prop :=
  ∀ A : RegularAtlas k X d,
    letI := A.chartedSpace
    IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k X k)

/-- Families from arbitrary real smooth manifolds are tested by all global
regular functions, for the charted space constructed from the regular atlas. -/
def regularAtlasFamilyCriterionStatement : Prop :=
  ∀ (A : RegularAtlas k X d)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type z} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M],
    letI := A.chartedSpace
    ∀ f : M → RingPoint k X k,
      ContMDiff I 𝓘(ℝ, Fin d → k) ∞ f ↔ RegularSmooth I f

/-- The independent analytic obligations for regular-atlas output data. -/
def regularAtlasComparisonStatement : Prop :=
  regularAtlasManifoldStatement k X d ∧
    regularAtlasFamilyCriterionStatement.{v, w, z} k X d

end Langlands.AlgebraicGeometry.PointManifold
