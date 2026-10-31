import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A local closed-immersion criterion at a rational point for proper morphisms

Let `K` be an algebraically closed field and let `f : X ⟶ Y` be a proper morphism of
schemes locally of finite type over `K`. If a rational point `x` of `X` is the only
rational point of `X` with its image, and no nonzero rational tangent vector at `x` is
killed by `f`, then `f` is a closed immersion over some open neighbourhood of `f x` in `Y`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A proper morphism is a closed immersion near the image of a rational point
whose rational fibre is unique and whose rational tangent kernel is trivial. -/
def ProperRationalImmersionLocalClosedImmersionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) [IsProper f],
    f ≫ q = p →
    ∀ (x : Spec (CommRingCat.of K) ⟶ X), Picard.IsRationalPoint p x →
      (∀ (y : Spec (CommRingCat.of K) ⟶ X), Picard.IsRationalPoint p y →
        y ≫ f = x ≫ f → y = x) →
      (∀ (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X),
        Picard.IsTangentVectorAt p x t →
        t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f →
        t = Picard.dualNumberProjection K ≫ x) →
      ∃ V : Y.Opens,
        f.base (x.base (IsLocalRing.closedPoint K)) ∈ V ∧
        IsClosedImmersion (f ∣_ V)

end Langlands.AlgebraicGeometry
