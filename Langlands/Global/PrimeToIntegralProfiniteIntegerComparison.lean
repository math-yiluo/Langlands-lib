import Langlands.Global.ProfiniteIntegerRing
import Langlands.Global.PrimeToFiniteAdeles

/-! # Integral away comparison compatible with a supplied full comparison -/

namespace Langlands.Global

/-- Every normalized continuous full integral comparison descends, for every
natural modulus, to a normalized continuous away comparison compatible with
that supplied full equivalence. This proposition supplies no proof or chosen
comparison. -/
def PrimeToIntegralProfiniteIntegerAdeleComparisons : Prop :=
  ∀ (eFull : ProfiniteIntegerRing ≃+* integralFiniteAdeles ℚ),
    Continuous eFull → Continuous eFull.symm →
      (∀ z : ℤ, (eFull (ProfiniteIntegerRing.intCastHom z) : FiniteAdeles ℚ) =
        algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ)) →
      ∀ m : ℕ,
        ∃ e₀ : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m,
          Continuous e₀ ∧ Continuous e₀.symm ∧
            (∀ z : ℤ, (e₀ (PrimeToProfiniteIntegerRing.intCastHom m z) :
              PrimeToFiniteAdeles m) =
                algebraMap ℚ (PrimeToFiniteAdeles m) (z : ℚ)) ∧
            (∀ a : ProfiniteIntegerRing,
              e₀ (PrimeToProfiniteIntegerRing.restrict m a) =
                primeToIntegralRestriction m (eFull a))

end Langlands.Global
