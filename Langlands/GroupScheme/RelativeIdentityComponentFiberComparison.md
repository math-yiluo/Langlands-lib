# Comparing represented relative identity components with residue fibres

This internal comparison derives consequences of the published all-test
`IsRelativeIdentityComponent` predicate over an arbitrary base scheme in an
arbitrary universe. It requires no smoothness or affineness assumption.

`range_residueFiberPoint` identifies the range of a pulled-back test morphism
with the inverse image of its original range under the residue-fibre inclusion.
The proof identifies the actual pullback map and uses Mathlib's
`Scheme.Pullback.range_map`, with identity maps on the base and on its residue
field.

`inclusion_inRelativeIdentityComponent` applies the representation equivalence
to the subgroup inclusion itself, whose factorization is the identity map.
`range_residueFiberInclusion_subset` specializes its defining image condition.
These are internal consequences of the published definition and actual
scheme-pullback functoriality; no existence theorem for relative components is
assumed.

`preimage_range_inclusion_eq_identitySet` proves the reverse inclusion using
all test schemes. For a point in the identity component of a residue fibre,
take the spectrum of the residue field of its image in the total space as a
test scheme. Its range is that single total-space point. A fibre containing
that point must be the original fibre, and the fibre inclusion is injective.
Thus this test satisfies the identity-component condition at every point
of the base. The defining representation equivalence factors it through
the supplied subgroup, so its image point belongs to the subgroup image.
`range_residueFiberInclusion` combines this result with the pullback-range
formula to identify the actual base-changed homomorphism's range.

`isClosed_fiber_preimage_range_inclusion` transports this equality through
Mathlib's `Scheme.Hom.fiberHomeo`, proving closedness in the topological
fibre subspace. It uses the fact that every connected component is closed
and imposes no smoothness hypothesis. If the base point is closed,
`isClosed_inter_fiber_range_inclusion` makes the fibre inclusion a closed
embedding and deduces that the intersection with the subgroup image is
closed in the total space.

These lemmas are internal proof infrastructure for the published
`SmoothDvrAffinenessStatement`; this file does not yet prove that target.
