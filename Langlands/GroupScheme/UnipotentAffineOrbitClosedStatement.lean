import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The Kostant–Rosenlicht closed-orbit statement -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every rational-point orbit of a smooth affine unipotent group on an affine
algebraic scheme over an algebraically closed field is closed in the underlying
Zariski topology. This is the algebraically closed case of Milne 17.64. -/
def UnipotentAffineOrbitClosedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom],
    IsUnipotent U →
      ∀ (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
        [LocallyOfFiniteType X.hom] (a : SchemeAction U X)
        (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X),
        IsClosed (Set.range (a.act (𝟙 U.X) (toUnit U.X ≫ x)).left)

end Langlands.GroupScheme
