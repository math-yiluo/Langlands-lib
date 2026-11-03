import Langlands.GroupScheme.Rational.PointedCoordinateAction

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.PointedCoordinateWeights

/-- Target: a dominant affine morphism to a reduced target has injective
actual coordinate pullback. -/
def DominantPullbackStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (V W : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] [IsAffineHom W.hom]
    (f : V ⟶ W), IsReduced W.left → IsDominant f.left →
      Function.Injective (pullback f)

end Langlands.GroupScheme.PointedCoordinateWeights
