import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsor
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Existence of the integral inner-isomorphism torsor over a DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A prescribed generic isomorphism of reductive groups over a DVR belongs
to an actual integral torsor of inner-related isomorphisms. -/
def GenericInnerIsomorphismTorsorExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H),
    Nonempty (GenericInnerIsomorphismTorsor R K G H f)

end Langlands.GroupScheme
