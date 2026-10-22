import Langlands.Cohomology.Continuous.RestrictionMaps

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- The actual finite-stage and colimit restrictions agree with Mathlib's continuous restriction. -/
def RestrictionComparisonLaws : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : DiscreteModule k G) (H : OpenSubgroup G),
    (∀ N : OpenNormalSubgroup G,
      finiteRestrictionCochains A H N ≫
          finiteStageCochainMap (A.restrict H.toSubgroup) (restrictOpenNormal H N) =
        finiteStageCochainMap A N ≫ continuousRestrictionCochains A H.toSubgroup) ∧
    (∀ (N : OpenNormalSubgroup G) (q : ℕ),
      finiteRestriction A H N q ≫
          finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H N) q =
        finiteStageToContinuous A N q ≫
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (continuousRestriction A H.toSubgroup q)) ∧
    ∀ q : ℕ,
      finiteQuotientRestriction A H q ≫
          finiteQuotientComparison (A.restrict H.toSubgroup) q =
        finiteQuotientComparison A q ≫
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (continuousRestriction A H.toSubgroup q)

end Langlands.Continuous
