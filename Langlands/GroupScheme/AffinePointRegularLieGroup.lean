import Langlands.GroupScheme.AffinePointRegularSmooth
import Langlands.AlgebraicGeometry.PointManifold.RegularChartExistence
import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparison
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # Lie group operations from the regular-atlas family criterion -/

noncomputable section

universe v w

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

variable {k : Type} [RCLike k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable {d : ℕ}

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

/-- A regular atlas with the proved analytic comparison gives the original
actual point group a real smooth Lie group structure, on its existing topology. -/
theorem regularAtlasLieGroup (A : RegularAtlas k G.X d)
    (hcomparison : regularAtlasComparisonStatement.{0, 0, 0} k G.X d) :
    letI := A.chartedSpace
    LieGroup 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) := by
  let := A.chartedSpace
  let : IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) := hcomparison.1 A
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply (hcomparison.2 A (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mpr
    apply regularSmooth_mul (G := G)
    · exact (hcomparison.2 A (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mp
        contMDiff_fst
    · exact (hcomparison.2 A (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) _).mp
        contMDiff_snd
  · apply (hcomparison.2 A 𝓘(ℝ, Fin d → k) _).mpr
    apply regularSmooth_inv (G := G)
    exact (hcomparison.2 A 𝓘(ℝ, Fin d → k) _).mp contMDiff_id

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For a regular atlas satisfying the analytic family comparison, the group
family criterion is exactly `CoordinateSmooth` for identity coefficients. -/
theorem regularAtlas_contMDiff_iff_coordinateSmooth (A : RegularAtlas k G.X d)
    (hfamily : regularAtlasFamilyCriterionStatement.{v, v, w} k G.X d)
    (p : M → G.affinePoints (CommAlgCat.of k k)) :
    letI := A.chartedSpace
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p := by
  let := A.chartedSpace
  exact (hfamily A I _).trans (G.regularSmooth_iff_coordinateSmooth I p)

/-- The full actual-group target: algebraic constant relative dimension yields
a regular atlas, a Lie group on the original points, and the coordinate-family
criterion for the same atlas. This proposition does not assume analytic charts. -/
def smoothAffineGroupManifoldStatement : Prop :=
  SmoothOfRelativeDimension d G.X.hom →
    ∃ A : RegularAtlas k G.X d,
      letI := A.chartedSpace
      LieGroup 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) ∧
        ∀ {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
          {H' : Type v} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
          {M' : Type w} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
          (p : M' → G.affinePoints (CommAlgCat.of k k)),
          ContMDiff I' 𝓘(ℝ, Fin d → k) ∞
              (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) ↔
            G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I' p

/-- The real-point group target, with real model dimension `d`. -/
abbrev realSmoothAffineGroupManifoldStatement
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ) : Prop :=
  smoothAffineGroupManifoldStatement.{v, w} (k := ℝ) G (d := d)

/-- The complex-point group target, with real model dimension `2 * d`. -/
abbrev complexSmoothAffineGroupManifoldStatement
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ) : Prop :=
  smoothAffineGroupManifoldStatement.{v, w} (k := ℂ) G (d := d)

end Langlands.GroupScheme
