# The splitting norm is the actual group transfer

This internal comparison evaluates the norm of the concrete cocycle splitting
representation on the coinvariant class attached to an element of the actual
cocycle extension. Its value in the coefficient group equals Mathlib's
`MonoidHom.transfer` to the coefficient subgroup, followed by the original
coefficient-subgroup identification.

The proof expands the actual representation norm as the sum of all group
actions. The first coordinate of the action on `(a,e_h)` is `g a + c(g,h)`.
Consequently its sum is the additive form of the product
`product_g ((g • a) * c(g,h))`. The computation in
`CocycleExtensionTransfer` identifies that product with the actual coset-product
transfer. Both additive and multiplicative forms of this equality are provided.

`normOnExtension` is the corresponding homomorphism into the multiplicative
group of actual coefficient invariants. No cup-product bijectivity or
arithmetic hypothesis is required for the comparison.
