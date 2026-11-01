import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Factorial prime localizations of smooth algebras over DVRs -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every prime localization of every smooth algebra over a discrete valuation
ring has unique factorization. This defines the proposition, without proving it. -/
def SmoothDVRFactorialLocalizationsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Type u) [CommRing A] [Algebra R A],
    Algebra.Smooth R A → ∀ (P : Ideal A) [P.IsPrime],
      UniqueFactorizationMonoid (Localization.AtPrime P)

end Langlands.CommutativeAlgebra
