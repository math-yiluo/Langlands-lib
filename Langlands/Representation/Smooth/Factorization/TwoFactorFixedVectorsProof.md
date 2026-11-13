# Fixed vectors in an external tensor product

The theorem `Langlands.productFixedVectors` proves the published
`Langlands.ProductFixedVectorsStatement` over its four independent universes.
This is the algebraic fixed-vector prerequisite of Flath's Theorem 1
(`flath-1979-tensor-products`, printed pp.179–180), also used in Renard III.1.14
(`renard-2026-representations-groupes-reductifs-padiques`, printed pp.66–67).

Choose linear retractions of the two fixed-subspace inclusions. Their tensor
product is a left inverse of the canonical inclusion, proving injectivity.
For an invariant tensor, expansion against a basis of the second factor shows
that each first-factor coefficient is fixed. Hence the projection onto the
first fixed space fixes that tensor. The same argument with coefficients in
the first factor handles the second projection. Applying the tensor of the
two retractions therefore gives a preimage under the canonical inclusion.
Conversely, tensors of fixed vectors are fixed by the product subgroup,
and tensor induction extends this to their span.

The coefficient and projection lemmas are internal linear-algebra steps derived
for this proof. No topological or finite-dimensional hypothesis is used.
