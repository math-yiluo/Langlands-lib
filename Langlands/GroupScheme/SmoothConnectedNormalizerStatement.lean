import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The all-test normalizer of a smooth closed subgroup with geometrically
connected fibres in a smooth affine group has a finitely presented closed representative. -/
def SmoothConnectedNormalizerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (i : H ⟶ G),
    IsClosedSubgroup i → Smooth H.X.hom → GeometricallyConnected H.X.hom →
    ∃ (N : GroupScheme S) (j : N ⟶ G),
      IsClosedSubgroup j ∧ LocallyOfFinitePresentation j.hom.hom.left ∧
        (SubgroupFunctor.range i).normalizer.IsRepresentedBy j

end Langlands.GroupScheme
