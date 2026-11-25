# A rational Levi is the centralizer of its specified split component

`Langlands.GroupScheme.leviSplitComponentCentralizer` proves exactly
`Langlands.GroupScheme.LeviSplitComponentCentralizerStatement.{u}` from
`Rational.LeviSplitComponentRecallStatements`. For every field `k : Type u`,
connected reductive `G/k`, rational parabolic `j : P → G`, rational Levi
`l : L → P`, and specified split component `a : A → L`, it proves

`torusCentralizer (a ≫ l ≫ j) = SubgroupFunctor.range (l ≫ j)`.

This is equality of subgroup functors on every relative test scheme, including
the refinement condition in `torusCentralizer`. The field, universe, original
Levi inclusion and supplied split-component morphism are retained without any
additional hypothesis.

## Implemented proof

The proof composes two published Library results.

1. `ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup`
   supplies a ground-field cocharacter `χ : Gm → G` with
   `range j = Dynamic.parabolic χ`. Closedness of the given parabolic makes
   its underlying map monomorphic, so the original `j` represents this
   dynamic parabolic.
2. Apply
   `IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
   to this presentation, the original rational Levi and the specified split
   component. The last conjunct of its conclusion is the required equality.

The second result, in `Rational.OriginalLeviCocharacter`, projects the
presenting cocharacter through the retraction attached to the original Levi
decomposition. The resulting cocharacter of `L` is central and still presents
the same parabolic after its ambient inclusion. Every central homomorphism
from a split torus to `L` factors through the specified split component, by
`IsSplitComponent.exists_factor`. The original Levi is the dynamic centralizer
of the resulting cocharacter. The whole-component centralizer lies in that
cocharacter centralizer, and centrality of the component gives the reverse
inclusion of the Levi image. These are all-test subgroup-functor statements.
The imported theorem proves these steps; this module selects its final
conclusion.

## Provenance and scope

The target records the centralizer assertion recalled in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.3.1, printed pp.109–110 / PDF pp.115–116, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The statement's
paired Markdown documents the original source and the extension from Renard's
local field to arbitrary fields.

The implemented proof is an internal composition of the published results
above, whose source accounts and authorship remain in their paired Markdown.
It does not use the normalizer or finiteness assertions in the recall module,
or any downstream parabolic split-component target. No target or imported
source file is modified.
