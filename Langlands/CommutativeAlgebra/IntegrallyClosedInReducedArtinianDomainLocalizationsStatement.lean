import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Domain prime localizations of rings integrally closed in reduced Artinian rings -/

namespace Langlands.CommutativeAlgebra

/-- If `R` is integrally closed in a reduced Artinian ring `B` (with `R → B`
injective, as part of `IsIntegrallyClosedIn`), then every prime localization of `R`
is a domain. -/
def IntegrallyClosedInReducedArtinianDomainLocalizations.{u, v} : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B],
    IsIntegrallyClosedIn R B → IsReduced B → IsArtinianRing B →
      ∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p)

end Langlands.CommutativeAlgebra
