import Langlands.GroupScheme.Rational.PointedCoordinateAction
import Mathlib.Algebra.DirectSum.Module

/-! # Split-torus decomposition target for actual pointed affine coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.PointedCoordinateWeights

open Classical in
/-- The actual coordinate and fixed-point augmentation eigenspaces give
internal direct sums for every split-torus action on a pointed affine scheme. -/
def PointedCoordinateDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
    ∀ (V : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom]
      (a : PointedAction S V),
      DirectSum.IsInternal (weightSpace a) ∧
      DirectSum.IsInternal (augmentationWeightSpace a)

end Langlands.GroupScheme.PointedCoordinateWeights
