import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Domain prime localizations of smooth algebras over fields -/

namespace Langlands.CommutativeAlgebra

/-- Every prime localization of a smooth algebra over any field is a domain. -/
def SmoothAlgebraDomainLocalizations.{u, v} : Prop :=
  ∀ (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A],
    Algebra.Smooth K A →
      ∀ (p : Ideal A) [p.IsPrime], IsDomain (Localization.AtPrime p)

end Langlands.CommutativeAlgebra
