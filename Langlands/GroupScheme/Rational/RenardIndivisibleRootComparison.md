# Actual simple roots and indivisible positive indecomposables

This derived supporting result is conditional on `HasRelativeRootSystem i`,
splitness of the actual torus, and a generic cocharacter. It does not construct
the root-system witness for an arbitrary connected reductive group.

The actual root characters are identified with the indices of the given rational
root pairing by `RelativeRootCoxeter.rootIndexEquiv`. Injectivity of
rationalization for a split torus identifies natural-multiple relations in the
pairing with those among actual roots. It therefore identifies the restricted
indices of `RootPairing.indivisiblePairing` with actual indivisible roots.

The proof transfers indecomposability among the indivisible positive characters
to the restricted pairing. The generic `image_baseOf_indivisiblePairing`
comparison transfers it to the full pairing, and `mem_base_iff` identifies that
base with the published actual simple relative roots. Conversely, a simple root
is an indecomposable of the full pairing, hence indivisible, and it remains
indecomposable after restricting the allowed summands. No reducedness or
positive-rank assumption is used.

The proposition `RelativeRoot.IndivisiblePositiveRootComparison` packages this
comparison, and `HasRelativeRootSystem.indivisiblePositiveRootComparison` proves
it under the hypotheses above. Provenance is internal composition of the
published character/root-index correspondence with the derived indivisible
pairing result; no new assertion from the literature is used.

`RenardRootConventionFromRootSystemStatement` is the implication from the
published `RelativeRootSystemStatement` to the unchanged
`RenardRootConventionStatement`. The theorem
`renardRootConventionStatement_of_relativeRootSystem` proves this implication.
For each connected reductive group, smoothness supplies local finite type,
maximal splitness supplies splitness and the monomorphism, and the earlier
radical-weight theorem gives the first three comparisons. The fourth follows
from the conditional comparison above. This implication leaves the structural
root-system theorem as an explicit unresolved dependency and does not prove the
unconditional host proposition.
