import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # A local criterion for etaleness over a geometrically unibranch domain -/

universe u v w

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

/-- Domain-source specialization of Stacks Project tag 0GSC, allowing an
arbitrary model of the localization of the base at the contracted prime.
This definition states the proposition and supplies no proof of it. -/
def UnramifiedGeometricallyUnibranchLocalCriterionStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (Rp : Type w)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [Algebra.FormallyUnramified R S]
    (q : Ideal S) [q.IsPrime]
    [CommRing Rp] [IsDomain Rp] [IsLocalRing Rp] [Algebra R Rp]
    [IsLocalization.AtPrime Rp (q.under R)],
    GeometricallyUnibranchDomain Rp →
      Function.Injective (algebraMap R S) →
        ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)

end Langlands.AlgebraicGeometry
