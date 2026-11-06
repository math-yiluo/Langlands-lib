import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Self-normalization of a smooth closed geometrically connected subgroup of a
smooth affine group can be detected after every field-valued base change. -/
def RelativeSelfNormalizerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (i : H ⟶ G),
    IsClosedSubgroup i → Smooth H.X.hom → GeometricallyConnected H.X.hom →
    (∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).normalizer =
        SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) →
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i

end Langlands.GroupScheme
