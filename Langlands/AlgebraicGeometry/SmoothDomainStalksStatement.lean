import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Domain stalks of smooth schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every stalk of a scheme smooth over any field is a domain. -/
def SmoothDomainStalks : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)),
    Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x)

end Langlands.AlgebraicGeometry
