# Conditional assembly of the actual Dynamic ordered root product

`DynamicRootOrderedProductFromSemigroups` states an internal conditional reduction.
`dynamicRootOrderedProduct_of_semigroupStatements` proves that reduction and
assembles the exact published
`DynamicRootOrderedProductStatement` from explicit structural premises:
`SemigroupRealizationStatement`, `SemigroupOrderedProductStatement`,
`RelativeRootRayDecompositionStatement`, `DynamicSemigroupComparisonStatement`,
and the cyclic-semigroup comparison for actual roots of a connected reductive
group with a maximal split torus. It proves this implication only. It does not
prove any of those premises or supply the unconditional target proof.

`dynamicRootOrderedProduct_of_splitUnipotentSourceProducts` factors this
construction through a smaller source premise: ordered semigroup products
are required only for smooth connected affine groups which are both
unipotent and split unipotent, with their supplied split-torus actions.
The realization, ray-decomposition, Dynamic-comparison and actual-root
cyclic-comparison premises remain explicit. The original theorem and its
`DynamicRootOrderedProductFromSemigroups` definition keep their original
complete types. The original theorem supplies the smaller source premise
from its general solvable ordered-product premise, using the published
uniform all-test solvability of split-unipotent groups.

For the given arbitrary cocharacter, semigroup realization represents the
strictly positive conjugation semigroup by a smooth connected closed subgroup
`jU : U ⟶ G`. Positivity excludes zero, so the realization premise makes `U`
unipotent and split unipotent. The published split-series argument makes it
solvable on all scheme tests. The represented stable subgroup inherits the
torus action, and closedness makes its structure morphism affine.

Equivariant weight-support transport and the exact positive-support identity
identify the total support of this action on `U` with the actual positive roots.
The supplied root-ray cover, reindexed by the given enumeration, partitions that
support into `rootRayBlock` sets. Their disjointness and cross-exclusion are
exactly the hypotheses of the source ordered semigroup product premise. Applying it
inside `U` gives smooth connected closed factors and an isomorphism for their
actual ordered multiplication.

Each block generates its full positive cyclic tail. Its ambient semigroup
subgroup lies in the positive semigroup subgroup by monotonicity. Therefore
equivariant closed-inclusion transport identifies the image of each internal
factor with the ambient cyclic semigroup subgroup. The explicit comparison
premise identifies that subgroup with the full actual relative-root subgroup.
Ambient realization gives the same factor's unipotence and split unipotence,
and closed immersions compose.

The isomorphism is the internal ordered multiplication itself, viewed as an
isomorphism by `asIso`. Postcomposition with `jU` is the exact ambient
`orderedMultiplication` by its composition theorem. No condition on the order,
nonemptiness, or regularity of the cocharacter is used. The factors are full
root subgroups, so a multipliable root retains its doubled-root subgroup inside
its indivisible-root factor.

Provenance is internal: the proof composes the existing all-test subgroup,
represented-action, support, root-ray, semigroup transport and split-series
interfaces. The source structural assertions remain explicit inputs rather
than unproved claims about CGP or Kaletha–Prasad.
