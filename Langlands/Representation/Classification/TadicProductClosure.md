# Assembly of actual products of Tadic building blocks

Author: Worker 1745.

This internal unit packages the existential conclusion of the published
`TadicUnitaryDualExhaustion` and proves its algebraic closure properties.
It is derived from `TadicUnitaryStatement` and the published actual
`orderedProductRegrouping` theorem. It introduces no assertion from original
literature.

`HasTadicFactorization π` means that `π` is isomorphic to the entire
normalized upper-block induction of a finite family satisfying the existing
`IsTadicBuildingBlock` predicate. The definition retains the exact Speh and
same-representation complementary alternatives, strict complementary interval,
and explicit rank equalities of that predicate. Field and representation
universes remain independent, with actual smooth carriers in
`Type (max uF uV)`.

`isTadicBuildingBlock_of_iso` composes the isomorphism in either existing
building-block alternative with the supplied isomorphism.
`HasTadicFactorization.of_iso` composes the inverse of the supplied
isomorphism with the complete product presentation.
`HasTadicFactorization.rank_transport` eliminates an equality of ranks.

`hasTadicFactorization_normalizedProduct` chooses a presentation for each
factor of a supplied normalized product. It flattens the ordered block
refinement using `BlockShape.flatten`, carrying the original building-block
representations and their proofs to the resulting indices. The published
`orderedProductRegrouping` identifies this flattened induction with the
outer induction of the inner inductions. Equality transport at each inner
rank is resolved by the inverse law of `flattenBlockEquiv`. Functorial images
of the individual isomorphisms then identify the supplied outer product
with this complete flattened product.

The closure theorem assumes a complete factorization for each supplied
factor. It adds no irreducibility, unitarity, ordering, or analytic premise.
It does not prove that an arbitrary irreducible unitarizable representation
has such a factorization; the inductive exhaustion argument remains a
separate obligation.
