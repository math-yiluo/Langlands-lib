import Langlands.GroupScheme.IsomorphismScheme
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Group-isomorphism schemes for generically isomorphic reductive DVR groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The full natural isomorphism functor of generically isomorphic reductive
groups over a DVR is represented by an actual scheme. -/
def GenericIsomorphismSchemeExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (_f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H),
    Nonempty (GroupIsomorphismScheme G H)

end Langlands.GroupScheme
