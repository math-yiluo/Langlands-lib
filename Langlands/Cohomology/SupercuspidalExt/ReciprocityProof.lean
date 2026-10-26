import Langlands.Cohomology.SupercuspidalExt.Statement
import Langlands.Cohomology.SupercuspidalExt.Reciprocity

/-!
# Ext reciprocity for compact induction

The published natural isomorphism `extCompactInductionIso` supplies a witness
for every instance of `CompactInductionExtReciprocityStatement`.
-/

namespace Langlands.Cohomology.SupercuspidalExt

universe u

/-- Ext reciprocity for compact induction from an open subgroup, over any
commutative ring, in the common universe of the ring, group and representations. -/
theorem compactInductionExtReciprocity
    (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CompactInductionExtReciprocityStatement R G :=
  fun _ hH V n => ⟨extCompactInductionIso R hH V n⟩

end Langlands.Cohomology.SupercuspidalExt
