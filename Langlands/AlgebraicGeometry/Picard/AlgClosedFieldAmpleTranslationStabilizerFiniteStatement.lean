import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finitely many rational translations preserve an ample line bundle over an
algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- On an abelian scheme over an algebraically closed field, only finitely many rational
points `x` satisfy `t_x^* L ≅ L` for an ample line bundle `L`.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldAmpleTranslationStabilizerFiniteStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left),
    L.IsAmple →
      Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X //
        Nonempty ((LineBundle.pullback
          (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}

end Langlands.AbelianScheme
