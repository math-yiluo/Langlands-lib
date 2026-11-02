# Reindexing finite related tuples

This internal helper supplies the functoriality of the iterated fibre products
in Stacks Project, Decent Algebraic Spaces, Lemma 68.8.3 (Tag 0BBN).
That proof permutes the entries of related tuples before passing to the
distinct-tuple open subscheme and its symmetric-group quotient. The registered
source is `stacks-stratification-2026-11-02`. The construction also supports the
same argument used in Tag 07ST, registered as
`stacks-noetherian-approximation-2026-11-01`.

The mathematics here is derived from the universal property already established
in `EtaleEquivalenceRelationTuples`. As there, index `n` means `n + 1`
coordinates. This module does not construct the distinct-tuple locus or its
quotient.

`tupleLift` selects the unique morphism realizing any pairwise related family
of scheme-valued points. `tupleLift_projection` gives its coordinates, and
`tupleLift_unique` proves uniqueness by coordinate extensionality.
`comp_tupleLift` expresses compatibility with precomposition. Its two witnesses
of relatedness are arbitrary; coordinate extensionality ensures independence of
the selected witnesses.

`tupleReindex` constructs a morphism from a map of finite nonempty index sets.
The direction is contravariant: a function from the `m + 1` coordinates to the
`n + 1` coordinates gives a morphism from the `n + 1` tuple scheme to the
`m + 1` tuple scheme. `tupleReindex_projection`, `tupleReindex_id`, and
`tupleReindex_comp` prove the coordinate, identity, and composition laws.

`tupleReindexIso` uses inverse reindexing to give an isomorphism for every
bijection of index sets, including permutations. The two projection lemmas
describe its forward and inverse coordinate maps. The `refl`, `symm`, and
`trans` lemmas prove the corresponding isomorphism laws. All these proofs
reduce equality of morphisms to their coordinates.
