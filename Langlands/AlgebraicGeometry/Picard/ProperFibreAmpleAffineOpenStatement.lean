import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine neighbourhoods of finite sets in an ample fibre of a proper family -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Over a locally noetherian base, if a fixed line bundle on a proper family
is ample on the scheme-theoretic fibre at `s`, every finite set of points of
the total space lying over `s` lies in one affine open of the total space.
This proposition is a statement target, not a proof. -/
def ProperFibreAmpleAffineOpenStatement : Prop :=
  ∀ (X S : Scheme.{u}) [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X) (s : S),
    ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple →
      ∀ E : Finset X, (∀ x ∈ E, f x = s) →
        ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ E, x ∈ W

end Langlands.AlgebraicGeometry.Picard
