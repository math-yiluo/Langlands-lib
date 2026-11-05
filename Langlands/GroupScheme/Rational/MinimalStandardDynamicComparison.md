# The empty-index standard subgroups and a generic cocharacter

Author: Worker 1623.

This is an internal comparison for the canonical standard subgroup models used
in the adelic Siegel setup. For a connected reductive group over any field, a
maximal split torus `i : T → G`, and a generic cocharacter `ν`, it identifies
`standardParabolic i ν ∅` and `standardUnipotent i ν ∅` with the dynamic
parabolic and unipotent subgroup functors of `ν ≫ i`. The unipotent comparison
does not require genericity of `ν`. It also identifies
`standardLevi i ν ∅` with `torusCentralizer i`.

The comparisons are equalities of subgroup functors, hence hold on every test
scheme. `Standard.emptyParabolicDynamicIso` and
`Standard.emptyUnipotentDynamicIso` transport them to the actual affine
representatives. Their composition identities identify the inclusions into
the original ambient group. The result assumes neither a relative root system
nor negation stability of the root set. Empty root sets and split rank zero are
allowed.

The proof uses the already published actual-root inclusion theorem
`relativeRootSignInclusions`. The defining cocharacter `ν` is standard for the
empty index, so each standard intersection is contained in its dynamic subgroup.
In the other direction, genericity makes every nonnegative `ν`-root positive.
Every standard cocharacter is nonnegative on positive roots by
`IsStandardCocharacter.pairing_nonneg_of_positive`; this gives the parabolic
inclusion into every member of the intersection. For the unipotent comparison,
strict positivity on simple roots propagates to every positive root by
`positiveRelativeRoots_induction`. The Levi comparison applies the published
`genericCentralizer` theorem to
`standardLevi_empty_of_genericCentralizer`. The isomorphisms are the existing
uniqueness isomorphisms for two representatives of the same subgroup functor.

Provenance is derived: these are direct consequences of the Library's
standard-intersection definitions, positive-root induction, actual-root
inclusion theorem, generic-centralizer proof, and representability uniqueness.
No additional assertion is taken from the literature. In particular, this
module proves no geometric minimal-parabolic assertion, geometric radical
assertion, rational Levi decomposition, comparison of parabolic Lie roots,
derived/central split-torus product, compact-subgroup existence, or rational
Siegel coverage. It supplies structural comparisons for, and does not prove,
`AdelicGoodSiegelReductionStatement`.
