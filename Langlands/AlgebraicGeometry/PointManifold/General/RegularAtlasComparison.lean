import Langlands.AlgebraicGeometry.PointManifold.General.RegularCharts
import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparison
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Universe-general regular-atlas assembly and intrinsic families: exact targets -/

noncomputable section

universe u v w z

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable (k : Type u) [RCLike k]
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
    regularAtlasFamilyCriterionStatement.{u, v, w, z} k X d

section TypeZero

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [RCLike k]
  {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

/-- At Type 0, atlas assembly is precisely the published obligation under atlas conversion. -/
theorem regularAtlasManifoldStatement_typeZero_iff :
    regularAtlasManifoldStatement k X d ↔ PointManifold.regularAtlasManifoldStatement k X d := by
  constructor
  · intro h A
    exact h (RegularAtlas.typeZeroEquiv A)
  · intro h A
    exact h (RegularAtlas.typeZeroEquiv.symm A)

/-- The family obligation specializes with all three source universes still free. -/
theorem regularAtlasFamilyCriterionStatement_typeZero_iff :
    regularAtlasFamilyCriterionStatement.{0, v, w, z} k X d ↔
      PointManifold.regularAtlasFamilyCriterionStatement.{v, w, z} k X d := by
  constructor
  · intro h A E _ _ H _ I M _ _ _ f
    exact h (RegularAtlas.typeZeroEquiv A) I f
  · intro h A E _ _ H _ I M _ _ _ f
    exact h (RegularAtlas.typeZeroEquiv.symm A) I f

/-- The combined new obligation agrees with the frozen Type 0 target. -/
theorem regularAtlasComparisonStatement_typeZero_iff :
    regularAtlasComparisonStatement.{0, v, w, z} k X d ↔
      PointManifold.regularAtlasComparisonStatement.{v, w, z} k X d :=
  and_congr regularAtlasManifoldStatement_typeZero_iff
    regularAtlasFamilyCriterionStatement_typeZero_iff

end TypeZero

end Langlands.AlgebraicGeometry.PointManifold.General
