import Langlands.AlgebraicGeometry.CotangentDualNumber
import Langlands.AlgebraicGeometry.Picard.StalkTangentNaturality

/-! # A trivial rational tangent kernel forces cotangent surjectivity -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- At a rational point, a trivial kernel on actual dual-number tangents forces
surjectivity of the cotangent map induced by the actual scheme stalk map. -/
def TangentKernelCotangentSurjectivityStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (h : f ≫ q = p)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : Picard.IsRationalPoint p x),
    (∀ (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X),
      Picard.IsTangentVectorAt p x t →
      t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f →
      t = Picard.dualNumberProjection K ≫ x) →
    letI := Picard.stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := Picard.stalkAlgebraOver q (f (x (IsLocalRing.closedPoint K)))
    Function.Surjective
      (augmentationCotangentMap (Picard.rationalStalkAugmentation p x hx)
        (Picard.stalkMapAlgHomOver p q f h (x (IsLocalRing.closedPoint K))))

end Langlands.AlgebraicGeometry
