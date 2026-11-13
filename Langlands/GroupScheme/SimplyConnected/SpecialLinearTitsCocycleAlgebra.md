# All-test algebra of the special-linear Galois discrepancy

Author: Worker 187, for Task 6023.

This internal helper module proves algebraic identities for the cover,
coefficient maps and discrepancy defined in
`SimplyConnected.SpecialLinearTitsCocycleStatement`. It does not prove
`SpecialLinearTitsCocycleStatement` or assume a classification statement.
The fields and their common universe are arbitrary; neither finiteness
nor the Galois property of the extension is needed for these identities.

`coverAut_one` and `coverAut_mul` lift the published spectrum-map
identities to the category of schemes over `Spec K`. The latter fixes the
composition order: `coverAut (σ * τ) = coverAut σ ≫ coverAut τ`.

`coefficients_naturality` says that a map of relative test schemes pulls
back the coefficient homomorphism through its map on global sections.
`coefficients_coverAut` says that changing a cover point by `Spec σ`
precomposes its coefficient homomorphism by `σ`. The proof uses the
naturality of the inverse of the spectrum/global-sections comparison.

`discrepancyAut E σ a` packages the published discrepancy as an actual
group automorphism on determinant-one matrices over the global sections
of the test scheme. It is the composition of the special-linear point
comparison, the local isomorphism at `a ≫ Spec σ`, the inverse local
isomorphism at `a`, and the inverse point comparison.
`discrepancyAut_apply` identifies it with the existing function.

`discrepancy_one` cancels the local isomorphism with its inverse.
`discrepancy_mul` cancels the two intermediate comparisons and local
isomorphisms to obtain
`δ(σ * τ, a) = δ(σ, a) ∘ δ(τ, a ≫ Spec σ)`.
`discrepancy_naturality` combines the naturality of the special-linear
point comparison with that of the local isomorphism and its inverse.
Every identity holds on every relative test scheme and cover point.

Provenance: internal algebra of the published definitions. No new
literature claim or automorphism classification is used.
