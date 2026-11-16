import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.OuterIsomorphismScheme
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual outer-isomorphism quotients for reductive groups over a DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A supplied full-centre adjoint quotient acts on the actual isomorphism
scheme with a representable fpqc quotient and exact all-test inner orbits. -/
def GenericOuterIsomorphismSchemeExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (_f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H)
      (A : GroupScheme (Spec (CommRingCat.of R))) (q : G ⟶ A)
      (hq : IsRelativeAdjointQuotient q) (I : GroupIsomorphismScheme G H),
    Nonempty (OuterIsomorphismScheme I hq.innerAction)

end Langlands.GroupScheme
