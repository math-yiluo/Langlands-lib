import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Proper morphisms injective on rational points and tangent vectors

Let `K` be an algebraically closed field and let `f : X ⟶ Y` be a proper morphism of
schemes locally of finite type over `K`. If `f` is injective on `K`-points and every
rational tangent vector of `X` killed by `f` is zero, then `f` is a closed immersion.
Tangent vectors are the `K[ε]`-points of the imported module
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A proper morphism with injective rational points and trivial rational tangent
kernels is a closed immersion. -/
def ProperRationalImmersionClosedImmersionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) [IsProper f],
    f ≫ q = p →
    (∀ (x y : Spec (CommRingCat.of K) ⟶ X),
      Picard.IsRationalPoint p x → Picard.IsRationalPoint p y →
      x ≫ f = y ≫ f → x = y) →
    (∀ (x : Spec (CommRingCat.of K) ⟶ X), Picard.IsRationalPoint p x →
      ∀ (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X),
        Picard.IsTangentVectorAt p x t →
        t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f →
        t = Picard.dualNumberProjection K ≫ x) →
    IsClosedImmersion f

end Langlands.AlgebraicGeometry
