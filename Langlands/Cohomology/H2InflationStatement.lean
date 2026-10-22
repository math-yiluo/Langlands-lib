import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Degree-two inflation–restriction under degree-one vanishing -/

namespace Langlands.Cohomology

universe u

/-- If the first cohomology of a normal subgroup vanishes, inflation in
degree two is injective and its image is the kernel of restriction. -/
def H2InflationRestrictionExactness : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal],
    Subsingleton (groupCohomology (Rep.res S.subtype A) 1) →
      Function.Injective (groupCohomology.HInfRes A S 2).f ∧
        LinearMap.range (groupCohomology.HInfRes A S 2).f.hom =
          LinearMap.ker (groupCohomology.HInfRes A S 2).g.hom

end Langlands.Cohomology
