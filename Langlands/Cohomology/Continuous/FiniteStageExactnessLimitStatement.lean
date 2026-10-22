import Langlands.Cohomology.Continuous.RestrictionMaps

/-! # Exactness from finite stages of continuous cohomology -/

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- Finite-stage inflation and restriction exactness passes to the actual
continuous cohomology maps. -/
def FiniteStageExactnessLimit : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (H : OpenNormalSubgroup G) (q : ℕ),
    (∀ (N : OpenNormalSubgroup G) (h : N ≤ H),
      Function.Injective (finiteInflation A.toRep q h) ∧
        LinearMap.range (finiteInflation A.toRep q h).hom =
          LinearMap.ker (finiteRestriction A H.toOpenSubgroup N q).hom) →
    Function.Injective (finiteStageToContinuous A H q) ∧
      LinearMap.range (finiteStageToContinuous A H q).hom =
        LinearMap.ker
          ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (continuousRestriction A H.toSubgroup q)).hom

end Langlands.Continuous
