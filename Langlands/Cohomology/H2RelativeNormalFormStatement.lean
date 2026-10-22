import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Relative degree-two cocycle normal form and inflation injectivity -/

namespace Langlands.Cohomology

universe u

/-- An internal normal-form target: a two-cocycle whose restriction is a
coboundary can be adjusted to vanish when either argument lies in the normal
subgroup, provided the subgroup's first cohomology vanishes. -/
def H2RelativeCocycleNormalForm : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal],
    Subsingleton (groupCohomology (Rep.res S.subtype A) 1) →
      ∀ c : groupCohomology.cocycles₂ A,
        (∃ a : S → A, ∀ s t : S,
          c (s.1, t.1) = (groupCohomology.d₁₂ (Rep.res S.subtype A) a) (s, t)) →
        ∃ b : G → A, ∀ (s : S) (g : G),
          c (s.1, g) = (groupCohomology.d₁₂ A b) (s.1, g) ∧
          c (g, s.1) = (groupCohomology.d₁₂ A b) (g, s.1)

/-- The injectivity part of degree-two inflation–restriction under vanishing
of the normal subgroup's first cohomology. -/
def H2InflationInjectivity : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal],
    Subsingleton (groupCohomology (Rep.res S.subtype A) 1) →
      Function.Injective (groupCohomology.HInfRes A S 2).f

end Langlands.Cohomology
