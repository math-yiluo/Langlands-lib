# Automorphism topology from full represented domain spectral tests

For a complete ultrametric normed field `K` and an actual
`A : PresentedAffinoidAlgebra K`, this module constructs a topology on the group
`Aut A` of bounded algebra automorphisms. Its identity neighborhoods are generated
by the finite section-test subgroups of `DomainSpectralTests`. The declarations
are in `Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism`.

## Constructed group filter basis

`domainSpectralBasisSets A` consists of the underlying sets of
`finiteDomainSpectralSubgroup tests`, initially indexed by finite types in
`Type`. The data in each test remain in the universe of `K`: a supplied full
represented affinoid domain, an actual section of its positive-polyradius
quotient algebra, and a positive real tolerance. Each subgroup includes both
setwise preservation of every tested locus and the uniform spectral displacement
bounds on the tested sections.

`domainSpectralGroupFilterBasis A` supplies all `GroupFilterBasis` obligations.
The empty family makes the collection nonempty. Concatenating finite families
by their sum type gives the intersection of two basis subgroups. Each basis
subgroup contains the identity and is closed under multiplication and inversion
by the previously proved subgroup laws, so it can itself serve as the smaller
basis set for multiplication and inversion.

For conjugation by `g`, the proof transports every test by `g⁻¹`. The exact
finite-family transport identity identifies the resulting subgroup with the
conjugate by `g⁻¹` of the original one. Conjugating its elements by `g` cancels
the two inverse pairs and puts them back in the original subgroup. This proves
the remaining group-filter-basis axiom using the already constructed bounded
section operators and their full-map conjugation law.

## Topology and exact neighborhood criteria

`domainSpectralTopology A` is the topology produced by this group filter basis.
`domainSpectralTopology_isTopologicalGroup` proves that multiplication and
inversion are continuous for it. The topology and topological-group structure
are explicit declarations, not globally installed instances that would change
other uses of `Aut A`.

`mem_nhds_one_domainSpectralTopology` says that a set is a neighborhood of `1`
exactly when it contains the underlying set of some finite test subgroup.
`mem_nhds_domainSpectralTopology` gives the corresponding exact condition at
`g`: the set contains the image of some finite test subgroup under left
multiplication by `g`. Both include the empty family and follow directly from
the filter basis's neighborhood-basis theorems.

The initial use of `Type` for the finite index does not discard tests indexed
in another universe. `finiteDomainSpectralSubgroup_reindex` proves equality of
test subgroups under an equivalence of index types, by its surjectivity in one
direction and evaluation in the other. For an arbitrary finite index type,
`Finite.exists_equiv_fin` gives an equivalence with `Fin n` in `Type`.
`finiteDomainSpectralSubgroup_mem_basis` reindexes along its inverse and obtains
the identical subgroup as a member of the defined basis. The arbitrary index
universe is independent of that of `K`; no universe extension of the domain
representation property itself is asserted.

## Open tests and stabilizers

`finiteDomainSpectralSubgroup_mem_nhds_one` makes every finite test subgroup an
identity neighborhood, regardless of its finite index universe.
`isOpen_finiteDomainSpectralSubgroup` then uses the general fact that a subgroup
which is an identity neighborhood in a topological group is open.

`finiteDomainSpectralSubgroup_unit` identifies a family indexed by `Unit` with
its one test subgroup. `isOpen_domainSpectralSubgroup` uses that identity to
prove that each single test with a strictly positive tolerance is open.
Finally, `isOpen_locusStabilizer` tests the zero section with tolerance `1`;
the earlier zero-section identity makes this exactly the setwise stabilizer
of the represented locus. No pointwise fixation condition is imposed.

## Provenance and boundaries

This is an internal construction from the preceding full represented-domain
tests and Mathlib's group filter basis and open subgroup APIs. The proof pattern
for the basis, explicit topology, neighborhood criteria, and finite reindexing
adapts the published `StrictTestDomain.SpectralTopology`, with Worker 36
credited as coauthor. That earlier module ranges over unit-radius rational
presentations. The present module ranges over full represented domains over
arbitrary positive-polyradius presented algebras and uses the different
algebra-retaining base transport and its proved full-map identities. Neither
module is being replaced or silently identified with the other.

The construction allows trivial valuations, nilpotents, zero quotients and
empty loci. It is not a proof of separation of this topology. It neither
constructs all compact analytic domains nor proves that their section tests give
the same topology. Continuity of a given external group homomorphism into this
topology, comparison with norm-continuous actions, general analytic spaces,
structure sheaves and equivariant sites are separate obligations. No such
comparison or continuity assumption is needed to construct this topology.
