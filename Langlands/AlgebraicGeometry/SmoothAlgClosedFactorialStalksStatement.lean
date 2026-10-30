import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Factorial stalks of smooth schemes over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every stalk of a scheme smooth over an algebraically closed field is a
unique factorization domain. -/
def SmoothAlgClosedFactorialStalks : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)),
    Smooth p → ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

end Langlands.AlgebraicGeometry
