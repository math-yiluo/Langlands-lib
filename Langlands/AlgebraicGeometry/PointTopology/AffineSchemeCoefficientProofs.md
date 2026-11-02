# Proofs for coefficient change on actual affine scheme points

Author: Worker 105.

This proves `AffineSchemeCoefficientProperties`, the actual-scheme
coefficient-change assertions derived from Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 2.2, printed
page 3, and Proposition 2.1, printed page 2. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The comparison reuses `affineSchemePointEquiv_changeRing` from
[AffineProductRingTopologyProof](AffineProductRingTopologyProof.md), whose
proof is due to Worker 208. Actual precomposition with Spec f corresponds
to composition of algebra maps with f by `Spec.preimage_comp` and
`Spec.preimage_map`. Passing through the canonical affine-scheme isomorphism
preserves this naturality by associativity. Thus the comparison uses the
actual test-ring map and its correct direction.

The resulting equality expresses `RingPoint.changeRing f` as the
coefficient map on algebra points conjugated by the published actual point
homeomorphisms. Continuity, embeddings and closed embeddings follow by
composition from `AlgPoint.continuous_mapCoefficients`,
`AlgPoint.isEmbedding_mapCoefficients` and
`AlgPoint.isClosedEmbedding_mapCoefficients`.

For the open-embedding branch, the actual affine global-section
finite-type instance supplies finite type of the coordinate algebra.
The published `AlgPoint.isOpenEmbedding_mapCoefficients` gives the
coordinate conclusion, transported through the same homeomorphisms.
For discreteness, `affineDiscreteProperty_proof` supplies the coordinate
instance and the embedding underlying the point homeomorphism transfers it
to actual scheme points. The final theorem assembles exactly the target,
with topological-ring and discrete hypotheses scoped to their branches.

The statements and proof use a common arbitrary universe. They require no
topology on the coefficient ring R. The statement Markdown explains the
relative scope, the reversal in the printed inclusion in Example 2.2, and
the separate arithmetic and Weil-restriction obligations.
