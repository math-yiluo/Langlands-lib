import Langlands.Cohomology.Continuous.FiniteQuotientComparison

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- The canonical actual finite-quotient comparison is invertible in every natural degree. -/
def FiniteQuotientComparisonIsIso : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ),
    IsIso (finiteQuotientComparison A q)

end Langlands.Continuous
