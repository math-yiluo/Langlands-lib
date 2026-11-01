# Transport of scalar sections and descent on actual rational quotients

Worker 101's internal construction, using the published `ScalarCoverDescent`
interface authored by Workers 572 and 146. The module imports that interface
from the Library; it does not duplicate the dependency's source pair.

The existing `StandardRationalLaurentReduction.locusEquiv h` supplies the
bounded algebra equivalence between actual quotient algebras when their
actual rational loci agree. This module reuses that construction directly;
the duplicate `RationalData.equalLocusEquiv` definition has been removed.
The two maps are the restrictions of the two locus inclusions. Uniqueness of
bounded maps from each rational quotient proves the inverse equations. Both
directions commute with the actual maps from the presented base.

`scalarSectionsLocusEquiv` applies those equivalences componentwise to actual
scalar families. `scalarSectionsReindex` transports dependent families along
an equivalence of their index types. The index universes are independent of
the base and field universe.

`CompatibleScalarSections.map` uses the common-target lemma from
`ScalarCoverDescent` to show that any componentwise bounded maps over the same
base preserve ordered-pair intersection compatibility. This gives compatibility
for each of the two section transports.

`ScalarCoverDescent.reindex` and `reindex_iff` transfer unique scalar lifting
along an index equivalence. The proof transports a family back to the original
indices, applies the descent premise and uses surjectivity of the equivalence
to recover every equation and the uniqueness assertion.

`ScalarCoverDescent.of_locus_eq` and `locus_eq_iff` transfer descent between
pointwise equal actual loci. The proof pulls sections back by the inverse
bounded equivalences, applies the original descent premise and transports the
lift equations forward. Uniqueness follows by pulling a purported second lift
back. `of_reindex_locus_eq` combines these two transfers.

`ScalarCoverDescent.of_castSucc` adds a final quotient whose algebra is a
subsingleton to a descending family indexed by `Fin n`. Restriction to the
first `n` entries preserves compatibility. Their unique lift automatically
satisfies the last equation; its uniqueness follows from the first `n`
equations. This includes `n = 0`.
`of_castSucc_locus_empty` obtains the subsingleton instance from the published
empty-locus theorem.

`tuple_no_common_zero_reindex` transports the no-common-zero hypothesis
through a finite index equivalence. `standardRational_locus_reindex` proves
equality of actual standard rational loci by transporting the universal
inequalities through that equivalence. `ScalarCoverDescent.standard_reindex_iff`
then transports descent for a standard cover even though reindexing also
changes the numerator tuple in every quotient presentation. Its witnesses
of the no-common-zero conditions may be arbitrary.

The universal variants reindex after each bounded base change and transport
equal loci using the published formula for the locus of a pullback.

These are internal formal consequences of actual rational representability
and explicit descent premises; no additional literature theorem is claimed.
All constructions retain the actual quotient carriers, base maps and ordered
intersection restrictions. Empty index types, zero and nonreduced bases and
empty rational loci are allowed. The module asserts no unconditional descent,
higher Cech exactness, admissibility, finite-module descent or arbitrary-radius
result.
