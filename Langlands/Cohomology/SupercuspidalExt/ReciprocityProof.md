# Ext reciprocity for compact induction

Author: Worker 631. Coauthor: Worker 61, who supplied the proof term in the
task's expected route and constructed the published isomorphism used here.

The theorem
`Langlands.Cohomology.SupercuspidalExt.compactInductionExtReciprocity`
proves the published proposition
`Langlands.Cohomology.SupercuspidalExt.CompactInductionExtReciprocityStatement`
from [the statement module](Statement.md).

Let `u` be any universe, `R : Type u` a commutative ring and `G : Type u` a
topological group, with instances `[Group G] [TopologicalSpace G]
[IsTopologicalGroup G]`. For every subgroup `H : Subgroup G` with
`hH : IsOpen (H : Set G)`, every smooth representation
`V : SmoothRep.{u, u, u} R H` and every `n : ℕ`, the conclusion is

```lean
Nonempty (SmoothExt.ext R G ((compactInduction R G H).obj V) n ≅
  restriction R G H ⋙ SmoothExt.ext R H V n)
```

Here `restriction` and `compactInduction` are the functors of the statement
module, and `SmoothExt.ext` is the right derived functor of equivariant Hom.
The isomorphism is natural in the smooth representation of `G` supplied as
the second Ext argument. The subgroup has its subspace topology. The theorem
retains the arbitrary common universe `u` and every hypothesis of the target.

The implemented proof is

```lean
fun _ hH V n => ⟨extCompactInductionIso R hH V n⟩
```

After introducing the four quantified arguments, it uses
`Langlands.Cohomology.SupercuspidalExt.extCompactInductionIso R hH V n`
from [the reciprocity construction](Reciprocity.md) as the witness for
`Nonempty`. That construction applies the derived-functor comparison to
Hom-level Frobenius reciprocity; restriction to the open subgroup is exact
and preserves injective objects. This module is a derived corollary of that
published construction. Its companion explains the original-source
motivation and the construction's proof.
