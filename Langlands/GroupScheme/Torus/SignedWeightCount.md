# Counting restricted signed weights

This internal prerequisite converts an independent decomposition indexed by the
signed vectors of an integral basis into the signed-pair count used in the
maximal split torus weight statement. It assumes the decomposition and its
multiplicities; it does not construct them geometrically.

For an integral basis `b : Basis ι ℤ L`, `signedWeight b (j,s)` is
`(s : ℤ) • b j`, where `s` is a unit of the integers. Applying the basis
coordinate map converts equality of signed weights into equality of nonzero
single-coordinate finitely supported functions. This proves
`signedWeight_injective`. The same coordinates show that every signed weight
is nonzero. `signedWeights b` is their finite image when `ι` is finite.

`sum_signedWeights` uses injectivity to sum over the original signed pairs.
When each multiplicity is one, restricting by an integer linear functional `f`
therefore counts exactly the pairs satisfying `(s : ℤ) * f (b j) = c`.
Inserting zero adds `d 0` precisely when `c = 0`.
`sum_filter_eq_signed_card_add_zero` allows a finite support `T` whose nonzero
part is exactly `signedWeights b`. If zero is absent, its multiplicity must be
zero. This covers a vanishing residual weight space as well as a nonzero one.

The existing `Langlands.Plancherel.finrank_biSup_eq_sum` proves finite additivity
of dimensions for any independent
family of subspaces over a division ring, by induction on the finite indexing
set. Independence makes each new subspace disjoint from the sum of the previous
ones, so the usual dimension formula for a supremum and intersection applies.
The unchanged declaration is shared with `ParabolicRootCone` through
[LinearAlgebra/SubmoduleFinrank](../../LinearAlgebra/SubmoduleFinrank.md),
keeping this application independent of the representation imports.

`finrank_biSup_eq_signed_card_add_zero` applies the count to the dimensions of
an independent family `W` of subspaces. It assumes every signed basis space
has dimension one and that the support outside zero consists of exactly these
weights. Finally, `finrank_zero_eq_sub` assumes the spaces span the ambient
space. Taking the zero functional gives the total dimension as
`2 * Fintype.card ι + finrank K (W 0)`, hence the residual dimension as the
ambient dimension minus twice the number of basis weights.

The provenance is internal: the proof uses basis coordinates, finite-sum
reindexing and the dimension formula for independent subspaces. It works over
any division ring for the dimension calculation and imposes no condition on
the characteristic or cardinality of a field.
