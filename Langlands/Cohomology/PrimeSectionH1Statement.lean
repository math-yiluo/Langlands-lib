import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Degree-one vanishing from prime-index normal sections -/

namespace Langlands.Cohomology

universe u

/-- If, for every subgroup `H` of a finite group and every normal subgroup
`N` of `H` of prime index, the first cohomology of `H ⧸ N` with coefficients
in the `N`-invariants of the restricted representation vanishes, then the
first cohomology of the whole group vanishes. -/
def PrimeSectionH1Vanishing : Prop :=
  ∀ (k : Type u) [CommRing k] (G : Type u) [Group G] [Finite G]
    (A : Rep.{u} k G),
    (∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], N.index.Prime →
      Subsingleton
        (groupCohomology ((Rep.res H.subtype A).quotientToInvariants N) 1)) →
      Subsingleton (groupCohomology A 1)

end Langlands.Cohomology
