# Open units in symmetric tuple cross-correspondences

This internal helper continues the symmetric-tuple construction in Stacks
Lemma 68.8.3, Tag 0BBN, registered as
`stacks-stratification-2026-11-02` (snapshot `0BBN.html`, proof).
It derives the open diagonal and clopen unit locus directly on the actual
scheme correspondences constructed in the preceding modules. The
source-descent input is the diagonal argument of
`FiniteEtaleSourceUnramified`, derived from the étale alternative of Stacks
Lemma 35.14.5, Tag 05B5, registered as
`stacks-smooth-etale-source-descent-2026-11-02`.

The general theorem `isOpenImmersion_section_of_open_diagonal` says that a
section `s : S → X` of `p : X → S` is an open immersion if the diagonal of
`p` is open. Its proof takes the pullback of that diagonal along the map
`X → X ×[S] X` with components the identity and `p ≫ s`.
The section supplies both projections of the resulting pullback square.
The proof checks its universal property explicitly.

Assume that the source map of the equivalence relation is separated and
both its object and relation schemes are affine. The two
`tupleSymmetricCrossLeft_diagonal_isOpenImmersion` and
`tupleSymmetricCrossRight_diagonal_isOpenImmersion` instances apply the
source-descent helper to the finite étale surjective ordered-cross quotient
map. Its composites with the symmetric endpoints equal the composites of
the ordered endpoints and their finite étale tuple quotient maps, hence
are étale. The two `formallyUnramified` instances follow from these open
diagonals. These conclusions need no proof of smoothness descent.

The remaining declarations also assume the original joint relation map
is a closed immersion. The symmetric unit is an open immersion because
it is a section of the left endpoint, which has open diagonal. It is a
closed immersion because its composite with the closed joint endpoint
map is the diagonal of the affine symmetric tuple scheme.
`tupleSymmetricUnitOpen` is its open image. The corresponding clopen
theorem combines the open and closed immersion conclusions.
`tupleSymmetricOffDiagonalOpen` is its open complement; it is clopen
and compact since the ambient symmetric cross scheme is affine.

Finally, `tupleSymmetricOffDiagonalOpen_left_mem_threshold` says that the
left endpoint of every point outside the unit image belongs to the next
symmetric threshold. The preceding reduced-locus module showed that a
point whose left endpoint avoids this threshold lies in the unit image;
the new assertion is its contrapositive.

All constructions allow an arbitrary universe `u`. The module proves the
stated open-diagonal, unit-locus and threshold conclusions. It does not
yet prove that the symmetric endpoints are étale or prove the Noetherian
first-level statement.
