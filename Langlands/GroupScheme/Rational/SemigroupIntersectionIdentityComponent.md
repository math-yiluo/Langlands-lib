# Smooth intersections and exact ambient Lie images

This internal helper proves that the all-test intersection of two semigroup
subgroups for the same split-torus action on a smooth affine field group is
smooth and closed, with exact Lie image the span of the ambient weight spaces
whose characters lie in both semigroups. The semigroups may contain zero.
The helper does not assert that the intersection is connected.

For smoothness, the first supplied closed representative inherits the torus
action from the ambient group. The pullback of the second subgroup is its
inverse image under this equivariant closed embedding. The published
`smooth_semigroup_comap_representative`, applied with the proved
`semigroupRealization`, makes the pullback smooth. Choosing the published
smooth connected closed representatives supplies the all-test smooth closed
intersection.

For the Lie image, the actual intersection is represented and stable. Its
support lies in each semigroup because its tangent image lies in the exact
Lie image of each subgroup. The published support/tangent equivalence then
bounds its entire tangent image by the weight span for the intersected
semigroup. Conversely the semigroup subgroup for the intersection lies in
both groups by monotonicity and has exactly that weight span as its Lie
image. These bounds give equality.

The derivation uses only the imported Library realization, transport,
intersection and weight-support theorems. Its purpose in the convex-root
intersection proof is to supply the smooth intersection and exact Lie image
needed by the published identity-component comparison. No connectedness
claim is included.
