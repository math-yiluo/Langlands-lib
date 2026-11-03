# Joint spanning by relative roots and restricted rational characters

For a connected reductive group scheme `G` over any field and any actual maximal
split torus `i : T.toGrp ⟶ G`, the proposition
`RelativeRootsRestrictedCharactersSpanStatement` says that the actual relative
roots and the restrictions to `T` of rational characters of `G` together span
`ℚ ⊗[ℤ] characterLattice T`. The theorem
`relativeRootsRestrictedCharactersSpan` proves this proposition at its complete
universe scope. There is no additional root-system realization, character
complement, character-restriction injectivity, or positive-rank premise.

The implemented proof first proves
`IsSplitComponent.rationalCharacterRestrictRat_surjective`: restriction to any
actual split component becomes surjective over `ℚ`, by the published finite-index
restriction theorem and `rationalization_surjective_of_finiteIndex`.

For `IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top`, choose
an actual split component `a : A.toGrp ⟶ G` and its actual factor `f : A ⟶ T`
through `i`. The published root-annihilator centrality theorem and
`IsSplitComponent.restriction_kernels_eq_relativeRootSpans` identify the kernel
of rational restriction from `T` to `A` with the actual relative-root span.
Given any rational character vector `x` of `T`, rational surjectivity of
restriction from `G` to `A` supplies `y` whose restriction agrees with that of
`x`. Functoriality of restriction then writes
`x = (x - rationalCharacterRestrictRat i y) + rationalCharacterRestrictRat i y`.
The first summand lies in that kernel and the second in the restriction range.
The existing `relativeRootSpan_sup_restrictionRange` converts this sum equality
to the stated joint span.

This is an internal consequence of the cited Library declarations, developed as
a structural prerequisite for rational-point Aubert compatibility. It does not
assert disjointness of the two subspaces, integral character-restriction
injectivity, a choice of Coxeter system, a simple-reflection pairing law, or any
representation-theoretic expansion. It introduces no new claim from the
original literature and does not prove the final Jacquet compatibility target.
