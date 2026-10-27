import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Translation-invariant line bundles as translation differences over an
algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- On an abelian scheme over an algebraically closed field, every translation-invariant
line bundle `P` is isomorphic to `t_x^* L ⊗ N` for some rational point `x`, where `L` is
ample and `N` is a chosen tensor inverse of `L`, identified by a supplied evaluation.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldTranslationDifferenceLiftingStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L N : LineBundle A.X.left)
    (_evaluation : tensorObj L.obj N.obj ≅ structureSheaf A.X.left)
    (P : LineBundle A.X.left),
    L.IsAmple → GroupScheme.IsTranslationInvariant A.toGrp P →
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
        Nonempty (LineBundle.tensor preservation
          ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L) N ≅ P)

end Langlands.AbelianScheme
