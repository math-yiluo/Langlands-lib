# Canonical Galois transport and descent of actual subproducts

Worker 166. This internal construction concerns an actual finite simply connected
almost-simple product presentation `D` of the base change of a group `G` from a
field `k` to a field `L`, all in an arbitrary universe. The base-changed ambient
group is smooth and affine, as required for the canonical factor action. No
perfectness, characteristic, degree, or finiteness hypothesis on the fields is
used in the transport results.

## All-test transport

`SubgroupFunctor.galoisTransport_monotone` observes that canonical transport
preserves inclusion of subgroup functors. The monoid-homomorphism composition
law and cancellation of inverse automorphisms give
`galoisTransport_inv_apply`. Together these construct the order isomorphism
`galoisTransportOrderIso`; its forward function is the existing canonical
`galoisTransport`, and its inverse transports by the inverse automorphism.

`D.galoisTransport_range_subproductInclusion` identifies the transported range
of the actual subproduct on a subset `s` with the actual subproduct on the image
of `s` under `D.galoisFactorIndex`. To prove one containment, inverse transport
reduces it to the factor-generation criterion for `s`. The canonical transported
range formula identifies each image factor, which belongs to the image
subproduct. The other containment follows by expressing each selected image
factor as the transport of an original selected factor and using monotonicity.
Thus an invariant subset gives an invariant actual range, as stated in
`D.galoisTransport_range_subproductInclusion_eq_self`.

## Actual descent

For `exists_subproduct_descent`, assume additionally that `L/k` is Galois and
that the original ambient group `G` is affine. The full defining-ideal descent
theorem `Descent.GaloisInvariantClosedSubgroup.exists_descent` applies to the
actual closed subproduct inclusion. It constructs an affine ground-field group
`H`, a closed homomorphism `j : H ⟶ G`, and an actual recovery isomorphism from
`H_L` to the subproduct. The base change of `j` is exactly the recovery
isomorphism followed by the original subproduct inclusion.

`exists_smoothConnectedNormal_subproduct_descent` retains the same exact recovery
identity and also proves smoothness, connectedness and all-test normality over
`k`. The recovery isomorphism transfers the subproduct's smoothness and
connectedness to `H_L`; the established faithfully flat reflection and
surjective-projection results transfer them to `H`. The range identity transfers
normality to the base-changed inclusion, and represented fpqc normality
reflection proves normality of `j`.

These are derived constructions using the existing product, canonical transport
and subgroup-descent interfaces. No external structural premise is introduced.
This module does not yet prove factor-action transitivity or the
Weil-restriction classification.
