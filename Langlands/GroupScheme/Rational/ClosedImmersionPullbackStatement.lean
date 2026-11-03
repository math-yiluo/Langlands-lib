import Langlands.GroupScheme.Rational.PointedCoordinateAction

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.PointedCoordinateWeights

/-- Target: split-torus equivariant closed immersions give the actual
coordinate and augmentation quotients, including weightwise lifts. -/
def ClosedImmersionPullbackStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
    ∀ (V W : Over (Spec (CommRingCat.of k))) [IsAffineHom V.hom] [IsAffineHom W.hom]
      (a : PointedAction S V) (b : PointedAction S W) (f : V ⟶ W)
      (hf : IsPointedEquivariant a b f), IsClosedImmersion f.left →
        Function.Surjective (pullback f) ∧
        Function.Surjective (augmentationPullback a b f hf) ∧
        (∀ χ : characterLattice S,
          (weightSpace b χ).map (pullback f).toLinearMap = weightSpace a χ) ∧
        HasWeightwiseLifts a b f hf ∧ support a ⊆ support b

end Langlands.GroupScheme.PointedCoordinateWeights
