# Finite sharp-fixer exchange over any field

This internal support draft for Task 6309 extends the published local-field
`RootFixerExchange` argument to an arbitrary field, connected reductive group,
maximal split torus, and supplied `KPApartmentData`. It uses no extra apartment
axiom. It is intended for the pending comparison proof and does not prove the
zero/sharp comparison or the final affine-root statement.

For any nonempty apartment subset, the rank-one exchange factors a product of
opposite root fixers into the reversed root fixers and a normalizer element in
the sharp fixer fixing the subset. At a chosen base point the two valuations
have nonnegative sum. For positive sum, generic rank-one factorization gives a
centralizer factor fixing the base point, hence every apartment point. The
valuation bounds transport the other factors to every point of the subset.
For zero sum, both valuations vanish. The valuation translations force the
opposite factor pair to have value zero at every point of the subset, so the
generic fixed-point theorem supplies the required normalizer factor.

For a finite nonempty subset, the published root-fixer commutator theorem and
the generic ray property discharge the hypotheses of
`RootGroupFamily.iSup_subset_mul_of_exchange`. This gives the product of the
negative-root fixer group, positive-root fixer group, and sharp normalizer
fixer for any generic cocharacter. The ray property is supplied by actual
rank-one factorization rather than an additional apartment axiom.

The provenance is the implemented argument of the published
`RootFixerExchange` and its already published arbitrary-field inputs in
`GenericPointSharpExchange`. Finiteness is used only for the commutator theorem;
the first rank-one exchange result holds for every nonempty subset.
