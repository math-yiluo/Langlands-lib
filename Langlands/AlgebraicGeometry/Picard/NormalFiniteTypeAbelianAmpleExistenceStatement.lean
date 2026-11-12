import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.RingTheory.FiniteType

/-! # Ample line bundles on abelian schemes over normal finite-type `ℤ`-domains -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every integrally closed domain `R` of finite type over `ℤ`, every abelian scheme over
`Spec R` has an ample line bundle on its total space. -/
def NormalFiniteTypeAbelianAmpleExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    ∃ L : LineBundle A.X.left, L.IsAmple

end Langlands.AlgebraicGeometry.Picard
