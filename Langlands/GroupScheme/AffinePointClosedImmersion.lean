import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs

/-! # Closed immersions on the actual affine group-point topology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}
variable (G H : GroupScheme (Spec R))
variable [IsAffine G.X.left] [IsAffine H.X.left]
variable (A : CommAlgCat.{u} R) [TopologicalSpace A]

/-- A genuine closed immersion embeds actual coefficient points. -/
theorem isEmbedding_affinePointsTarget (f : G ⟶ H)
    [IsClosedImmersion f.hom.hom.left] :
    IsEmbedding (G.affinePointsTarget f A) := by
  have h := (H.affinePointsRingPointHomeomorph A).symm.isEmbedding.comp
    ((isEmbedding_affineSchemePointMap R A f.hom.hom).comp
      (G.affinePointsRingPointHomeomorph A).isEmbedding)
  convert h using 1
  funext x
  change x ≫ f.hom.hom =
    (H.affinePointsRingPointHomeomorph A).symm
      ((G.affinePointsRingPointHomeomorph A x) ≫ f.hom.hom)
  rw [affinePointsRingPointHomeomorph_symm_apply, affinePointsRingPointHomeomorph_apply]

/-- Hausdorff coefficients make the image of a genuine closed immersion closed. -/
theorem isClosedEmbedding_affinePointsTarget [T2Space A] (f : G ⟶ H)
    [IsClosedImmersion f.hom.hom.left] :
    IsClosedEmbedding (G.affinePointsTarget f A) := by
  have h := (H.affinePointsRingPointHomeomorph A).symm.isClosedEmbedding.comp
    ((isClosedEmbedding_affineSchemePointMap R A f.hom.hom).comp
      (G.affinePointsRingPointHomeomorph A).isClosedEmbedding)
  convert h using 1
  funext x
  change x ≫ f.hom.hom =
    (H.affinePointsRingPointHomeomorph A).symm
      ((G.affinePointsRingPointHomeomorph A x) ≫ f.hom.hom)
  rw [affinePointsRingPointHomeomorph_symm_apply, affinePointsRingPointHomeomorph_apply]

end Langlands.GroupScheme
