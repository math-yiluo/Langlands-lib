# Actual additive inputs for associated-pair comparisons

Worker 1768. Worker 1679 identified the published character and proposed its
connection to the Hecke component interface.

This internal construction bundles the proved standard character from
[`CuspidalWhittaker/AdelicCharacter`](CuspidalWhittaker/AdelicCharacter.md) and
identifies its finite restrictions with the actual components required by
[`AssociatedFactorStatement`](AssociatedFactorStatement.md). It applies to
every number field `K : Type u`, without a supplied additive character or
adelic pairing equivalence.

`standardGlobalAdditiveCharacter K` has the underlying character
`CuspidalWhittaker.adelicCharacter K`. Its continuity and nontriviality follow
from that module's proved theorems. Its value on `diagonal K x` is one because
the diagonal is `algebraMap K (Adeles K)`.

`finiteAdditiveInclusion_eq_finiteToAdeles_finiteSingle` identifies the two
coordinate inclusions: both put zero at the infinite places and insert the
given value at one finite place, with zero at all other finite places.
Extensionality then identifies `finiteAdditiveRestriction` of the bundled
character with `CuspidalWhittaker.localCharacter`. The published nontriviality
theorem for the latter proves that every finite restriction is nontrivial.

`standardFiniteAdditiveComponent K v` bundles that restriction in the canonical
topology used by `Correspondence.NontrivialAdditiveCharacter`. Continuity is
transported from the actual completion topology using the proved equality
`CompletionPadic.completion_topology_eq v`; the two topology expressions need
not be definitionally equal. Its underlying character retains the original
values, so `IsCanonicalFiniteAdditiveComponent` follows directly from the
coordinate formula. The component agrees pointwise with the published local
character and is trivial on `v.adicCompletionIntegers K`.

The published `Correspondence.existsUnique_localSelfDualMeasure`
supplies existence and uniqueness of a self-dual additive Haar measure for
each component in that same canonical topology, with the Library's plus-sign
Fourier convention. Finally,
`exists_associatedAdditiveInputs` packages one global character, all its
canonical finite components, diagonal triviality and a simultaneous family of
self-dual Haar measures. The family uses the published
`Correspondence.localSelfDualHaar`, chosen from proved existence and uniqueness.

The module adds no assertion from the original literature: each proof
composes published constructions and identifies their actual coordinate maps.
It supplies additive witnesses for the Henniart comparison route; it does not
prove gamma comparison, construct local Weil maps or local-constant systems,
or prove `AssociatedSupercuspidalInductionStatement`.
