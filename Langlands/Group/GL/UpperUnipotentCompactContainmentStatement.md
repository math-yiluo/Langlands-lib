# Compact containment in the full upper-unipotent group

`Langlands.GeneralLinear.UpperUnipotentCompactContainmentStatement` states
that every compact subset of the actual upper-unitriangular group lies in
a compact open subgroup of that group. This file states the proposition;
it supplies no proof.

The closed proposition quantifies over every prime `p`, every algebraic
extension `F : PadicField.{uF} p`, every compatible realization
`T : F.TopologicalData`, every natural rank `n`, and every compact subset
`C` of `GeneralLinear.upperUnipotent n F.Carrier`. The field universe is
arbitrary. Both compactness and openness use the subgroup topology induced
by precisely `T.topology`. The conclusion provides an actual `OpenSubgroup`
`K`, compact as a subset of the upper-unipotent group, with `C ⊆ K`.
It assumes no exhaustion or containment theorem as part of the input.

The group is the published subgroup of `GeneralLinear n F.Carrier`:
all entries strictly below the diagonal are zero and all diagonal entries
are one. Rank zero and rank one are included; these groups are trivial,
so the conclusion is consistent with these boundary cases. The compact
subset may be empty.

## Original source and correspondence

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, Lemma III.3.1 and its proof,
printed/PDF page 3, gives arbitrarily large compact open subgroups in a
p-adic unipotent group. The proof first treats upper-unitriangular matrices
by conjugating with powers of a diagonal matrix whose entries are powers
of a uniformizer, and then passes to closed subgroups.

The present statement specializes that result to the actual full
upper-unitriangular matrix group over the project's p-adic fields.
Its compact-set quantifier spells out the containment meaning of
“arbitrarily large”: diagonal expansion bounds every entry of a given
compact set uniformly, so one compact open subgroup contains that set.
The rank-zero case is the trivial-group extension of the source's matrix
formulation. The choice of compatible `TopologicalData` records the
topology in which the assertion is made; the canonical realization is
one such choice.

Registered source: `casselman-2019-jacquet-module`. SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original page was read and its bytes checked. No errata file for this
source was present in the current Library when this statement was written.

## Relation to existing interfaces

`Langlands.Parabolic.unipotentFiniteContainment` proves containment of
finite subsets of block radicals, and
`Langlands.RankinSelberg.unipotent_exists_compact_open` proves containment
of one full upper-unipotent element in positive rank. Neither conclusion
is used here as if it already quantified over arbitrary compact subsets.
This new target asks for that compact-subset conclusion for the actual
full upper-unipotent group.

Once proved, forgetting the openness of `K` directly gives
`Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups` for this
subgroup of the general linear group. That is the intended input to the
published character-localization exactness target. This statement alone
establishes no exactness or Whittaker heredity theorem, and does not
assert a nested exhaustion or a canonical choice of containing subgroup.
