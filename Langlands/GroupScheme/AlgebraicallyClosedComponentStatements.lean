import Langlands.GroupScheme.IdentityComponentRationalQuotient
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Rational representatives of components over algebraically closed fields -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

/-- Over an algebraically closed field, every component of a locally finite type
actual group scheme has a rational representative. For smooth affine groups, the
published rational-component embedding is therefore bijective. -/
def AlgebraicallyClosedComponentComparisonStatement : Prop :=
  (∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom],
    Function.Surjective (pointComponent H)) ∧
  (∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    Function.Bijective (rationalComponentEmbedding H))

end Langlands.GroupScheme.IdentityComponent
