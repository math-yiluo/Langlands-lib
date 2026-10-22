import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# The cyclic degree-two cocycle-sum comparison

The statement compares the class of an arbitrary two-cocycle with Mathlib's fixed
finite cyclic resolution quotient map. Its proof is a separate obligation.
-/

open CategoryTheory

namespace Langlands.Cohomology.CyclicH2

universe u

/-- The generator cycle sum represents a two-cocycle under Mathlib's actual
finite cyclic resolution comparison, whenever it is supplied as a kernel element. -/
def CocycleSumComparison : Prop :=
  ∀ (k G : Type u) [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (c : groupCohomology.cocycles₂ A)
    (x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap),
    (x : A) = ∑ i ∈ Finset.range (Fintype.card G), c (g ^ i, g) →
      groupCohomology.H2π A c =
        Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide) x

end Langlands.Cohomology.CyclicH2
