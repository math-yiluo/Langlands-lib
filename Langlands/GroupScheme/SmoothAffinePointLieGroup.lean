import Langlands.AlgebraicGeometry.PointManifold.SmoothAffineManifold
import Langlands.GroupScheme.AffinePointRegularLieGroup

/-! # The original point group on the chosen smooth affine manifold -/

noncomputable section

universe v w

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

variable {k : Type} [RCLike k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable {d : ℕ}

local instance : Group (RingPoint k G.X k) :=
  G.ringPointGroup (CommAlgCat.of k k)

/-- The group-point alias is exactly the chosen general affine charted space. -/
abbrev smoothAffineGroupChartedSpace
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (Fin d → k) (RingPoint k G.X k) :=
  smoothAffineChartedSpace hsmooth

/-- The original point group is a Lie group for the named chosen charts. -/
theorem smoothAffineLieGroup
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    LieGroup 𝓘(ℝ, Fin d → k) ∞ (RingPoint k G.X k) :=
  regularAtlasLieGroup G (smoothAffineRegularAtlas hsmooth)
    (regularAtlasComparison.{0, 0, 0} k G.X d)

/-- Actual point multiplication is smooth for these same chosen charts. -/
theorem smoothAffine_contMDiff_mul
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k))
      𝓘(ℝ, Fin d → k) ∞
      (fun p : RingPoint k G.X k × RingPoint k G.X k => p.1 * p.2) := by
  let := smoothAffineChartedSpace hsmooth
  exact (G.smoothAffineLieGroup hsmooth).contMDiff_mul

/-- Actual point inversion is smooth for these same chosen charts. -/
theorem smoothAffine_contMDiff_inv
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin d → k) ∞
      (fun p : RingPoint k G.X k => p⁻¹) := by
  let := smoothAffineChartedSpace hsmooth
  exact (G.smoothAffineLieGroup hsmooth).contMDiff_inv

/-- The real point group uses the chosen real charts and the original group law. -/
theorem realSmoothAffineLieGroup
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := realSmoothAffineChartedSpace G.X d hsmooth
    LieGroup 𝓘(ℝ, Fin d → ℝ) ∞ (RingPoint ℝ G.X ℝ) :=
  G.smoothAffineLieGroup hsmooth

/-- The complex point group is a real Lie group on the chosen complex charts. -/
theorem complexSmoothAffineLieGroup
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := complexSmoothAffineChartedSpace G.X d hsmooth
    LieGroup 𝓘(ℝ, Fin d → ℂ) ∞ (RingPoint ℂ G.X ℂ) :=
  G.smoothAffineLieGroup hsmooth

local instance : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For the named chosen manifold, the family criterion is exactly the original
identity-coefficient coordinate criterion under the actual-carrier homeomorphism. -/
theorem smoothAffine_contMDiff_iff_coordinateSmooth
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of k k)) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of k k) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p :=
  (smoothAffine_contMDiff_iff_regularSmooth.{v, v, w} I hsmooth _).trans
    (G.regularSmooth_iff_coordinateSmooth I p)

/-- The chosen real point manifold has the identity-coefficient family criterion. -/
theorem realSmoothAffine_contMDiff_iff_coordinateSmooth
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of ℝ ℝ)) :
    letI := realSmoothAffineChartedSpace G.X d hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → ℝ) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of ℝ ℝ) (RingHom.id ℝ) I p :=
  G.smoothAffine_contMDiff_iff_coordinateSmooth I hsmooth p

/-- The chosen complex point manifold has the real smooth family criterion. -/
theorem complexSmoothAffine_contMDiff_iff_coordinateSmooth
    (G : GroupScheme (Spec (CommRingCat.of ℂ))) [IsAffine G.X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of ℂ ℂ)) :
    letI := complexSmoothAffineChartedSpace G.X d hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → ℂ) ∞
        (fun t => G.affinePointsRingPointHomeomorph (CommAlgCat.of ℂ ℂ) (p t)) ↔
      G.CoordinateSmooth (CommAlgCat.of ℂ ℂ) (RingHom.id ℂ) I p :=
  G.smoothAffine_contMDiff_iff_coordinateSmooth I hsmooth p

end Langlands.GroupScheme
