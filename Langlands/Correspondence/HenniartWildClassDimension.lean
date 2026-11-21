import Langlands.Correspondence.HenniartTameOrbitFormula

/-!
# Dimensions of irreducible representations of wild inertia
-/

namespace Langlands.Henniart

/-- Every irreducible complex representation of wild inertia in the Weil group of
a p-adic field, with open kernel, has dimension a power of `p`. -/
def WildClassRankPrimePowerStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (c : WildClasses.{uK, uW} K),
    ∃ a : ℕ, FiniteRepresentation.openKernelIrreducibleRank _ c = p ^ a

end Langlands.Henniart
