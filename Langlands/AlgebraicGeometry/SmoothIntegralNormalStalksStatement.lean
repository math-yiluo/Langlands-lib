import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Normal stalks of integral smooth schemes over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every stalk of an integral scheme smooth over a field is integrally closed
in its fraction field. The field need not be perfect or algebraically closed. -/
def SmoothIntegralNormalStalksStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of K)),
    Smooth p → ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

end Langlands.AlgebraicGeometry
