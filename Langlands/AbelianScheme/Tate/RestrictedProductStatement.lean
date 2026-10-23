import Langlands.AbelianScheme.Tate.RestrictedProduct

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeComparison
universe u
open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] primeFact
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- The full rational Tate module agrees with the actual restricted product
through precisely the canonical rational prime coordinates. -/
def RationalRestrictedProductComparison : Prop :=
  ∃ e : RationalFull G T ≃+ RationalRestrictedProduct G T,
    ∀ (v : RationalFull G T) (p : Nat.Primes),
      e v p = rationalFullToPrime G T (p : ℕ) v

/-- The analogous exact-coordinate comparison over retained primes. -/
def RationalAwayRestrictedProductComparison (m : ℕ) : Prop :=
  ∃ e : RationalAway G T m ≃+ RationalAwayRestrictedProduct G T m,
    ∀ (v : RationalAway G T m) (p : AwayPrime m),
      e v p = rationalAwayToPrime G T (p.val : ℕ) m p.property v

/-- Combined full and all-away algebraic comparison obligation. -/
def RationalRestrictedProductComparisons : Prop :=
  RationalRestrictedProductComparison G T ∧
    ∀ m : ℕ, RationalAwayRestrictedProductComparison G T m

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

abbrev RationalRestrictedProductComparison : Prop :=
  GroupScheme.Tate.PrimeComparison.RationalRestrictedProductComparison A.toGrp T

abbrev RationalAwayRestrictedProductComparison (m : ℕ) : Prop :=
  GroupScheme.Tate.PrimeComparison.RationalAwayRestrictedProductComparison A.toGrp T m

abbrev RationalRestrictedProductComparisons : Prop :=
  GroupScheme.Tate.PrimeComparison.RationalRestrictedProductComparisons A.toGrp T

end Langlands.AbelianScheme.Tate.PrimeComparison
