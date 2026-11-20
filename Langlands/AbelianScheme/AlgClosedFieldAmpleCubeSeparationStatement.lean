import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Lefschetz's theorem over an algebraically closed field: the cube of an ample
line bundle on an abelian variety separates points and tangent vectors -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- On an abelian scheme over an algebraically closed field `K`, the complete linear
system of the actual tensor cube `L ⊗ L ⊗ L` of an ample line bundle `L` has no
rational base point, separates distinct rational points, and separates nonzero
rational tangent vectors. This proposition is a statement target, not a proof. -/
def AlgClosedFieldAmpleCubeSeparationStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left),
    L.IsAmple →
      SeparatesPointsAndTangents A.X.hom
        ⟨tensorPow L.obj 3, tensorPow_isLocallyFreeRankOne _ L 3⟩

end Langlands.AbelianScheme
