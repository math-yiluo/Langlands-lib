# The affine complement of symmetric tuple units

This derived helper packages the unit complement for the symmetric tuple
construction in Stacks Lemma 68.8.3, Tag 0BBN, registered as
`stacks-stratification-2026-11-02` (snapshot `0BBN.html`, proof).
Its input is the clopen unit locus and the left-endpoint threshold
containment proved in `EtaleEquivalenceRelationTupleUnitLocus`.

Throughout, the étale equivalence relation has separated source map,
affine object and relation schemes, and closed joint endpoint map.
Every construction allows an arbitrary universe `u`.

`tupleSymmetricCrossUnit_swap` says that endpoint exchange preserves the
unit, by uniqueness of a symmetric cross arrow with given endpoints.
`tupleSymmetricCrossSwap_mem_offDiagonal` uses this and involutivity to show
that endpoint exchange preserves the complement of the unit.
Applying the existing left-endpoint threshold theorem to the exchanged
arrow gives `tupleSymmetricOffDiagonalOpen_right_mem_threshold`.

`tupleSymmetricOffDiagonalScheme` is the open scheme of nonidentity
self-correspondences, and `tupleSymmetricOffDiagonalι` is its inclusion.
The inclusion is closed as well as open, because the open is clopen.
Its source is therefore affine, as a closed subscheme of the affine
symmetric cross scheme.

`tupleSymmetricOffDiagonalSwap` restricts endpoint exchange to this
scheme. Its `ι` formula follows from the universal property of the open
inclusion. The `swap` formula proves involutivity by composing with that
monomorphism.

`tupleSymmetricOffDiagonalLeft` and `tupleSymmetricOffDiagonalRight`
factor the two endpoints through the next symmetric threshold open.
The pointwise threshold containments put their images inside that open;
the universal property of an open immersion supplies the two maps.
Their `ι` formulas identify the composites with the original endpoints.
The `Swap_left` and `Swap_right` formulas say that the restricted
involution exchanges these factored endpoints. They follow by cancellation
of the open inclusion and the corresponding original endpoint formulas.

`tupleSymmetricUnitOffDiagonalIsColimit` applies Mathlib's disjoint-open
coproduct criterion to the unit and its open complement. Their images
are complementary by construction. `tupleSymmetricUnitOffDiagonalIso`
is the resulting canonical isomorphism from the coproduct of the unit
source and the nonidentity scheme to the entire self-correspondence.
Its `inl` and `inr` formulas identify the component maps with the unit
and the complementary inclusion.

The module packages affine schemes, restricted maps and a disjoint-union
decomposition. It does not prove the Noetherian first-level statement.
