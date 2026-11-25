# Norm comparisons for coefficient tensor units

For fields `B` and `L` over `F`, `leftTensorUnit` sends a unit `b` of `B`
to the actual tensor unit `b ⊗ 1`. Automorphisms of the right coefficient
field fix its image, and extending that field commutes with this map.

When `B/F` is finite, the determinant tensor norm is equivariant under
coefficient automorphisms and commutes with extending the right factor.
Its value on `b ⊗ 1` is the image in `L` of the field norm of `b` from `B`
to `F`. The proof compares the norm after extension from the base field
and uses the actual tensor unit isomorphism over `F`.

When `B/F` is finite separable and embedded over `F` in a normal extension
`L/F`, the tensor norm is the product of the canonical embedding
coordinates. Putting a unit of `L` of `n`-th power one at the inclusion
coordinate and one at all the other coordinates gives a tensor unit of
`n`-th power one with the prescribed norm. These internal comparisons
are used to adjust a primitive to have norm one.
