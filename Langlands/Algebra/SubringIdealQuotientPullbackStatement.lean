import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Ideal.Quotient.Operations

open CategoryTheory

universe u

namespace Langlands.Algebra

/-- A subring containing an ideal of the ambient ring is the canonical pullback
of the ambient ring and the subring quotient over the ambient quotient. -/
def SubringIdealQuotientPullbackStatement : Prop :=
  ∀ (B : Type u) [CommRing B] (R : Subring B) (I : Ideal B),
    (I : Set B) ⊆ (R : Set B) →
      IsPullback
        (CommRingCat.ofHom R.subtype)
        (CommRingCat.ofHom (Ideal.Quotient.mk (I.comap R.subtype)))
        (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (CommRingCat.ofHom
          (Ideal.quotientMap (I := I.comap R.subtype) I R.subtype le_rfl))

end Langlands.Algebra
