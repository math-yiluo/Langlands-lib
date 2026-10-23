# Finite adelic general linear groups as a restricted product

This internal construction compares the existing matrix units over the finite
adele ring with Mathlib's cofinite restricted product of the existing local
matrix groups relative to `localIntegral`. It retains every natural rank,
including zero, and arbitrary universes for the number field.

The forward map evaluates entries at each finite place. Finiteness of the matrix
index set gives simultaneous integrality of all entries of both the matrix and
its inverse outside a finite set. Conversely, the integrality condition on a
restricted family supplies finite adeles entry by entry; the inverse family
supplies the inverse matrix. Evaluation at every place verifies both matrix
inverse equations and the two inverse-map identities.

The construction is derived from the definitions in `LocalFactor`,
`StandardIntegralStatement`, and Mathlib's restricted-product API. It introduces
no arithmetic existence assumptions or alternative topologies.

Continuity uses the existing topologies throughout. Each entry of the assembled
matrix is a continuous map of restricted products, by
`RestrictedProduct.mapAlong_continuous`. Applying the same argument to the
inverse family gives continuity into the matrix-units topology. In the forward
direction, evaluation restricted to the open subgroup `standardIntegral` factors
through the product of the local integral subgroups and the continuous
restricted-product structure map. Openness gives continuity at the identity in
the whole adelic group, and the homomorphism property gives continuity everywhere.

The bundled comparison is `restrictedProductEquiv`. Its forward coordinate is
exactly `localProjection`; `restrictedProductEquiv_symm_apply` and
`restrictedProductEquiv_symm_inv_apply` describe the entries of the assembled
matrix and its inverse. `restrictedProductEquiv_localInclusion` identifies the
existing local inclusion with Mathlib's `RestrictedProduct.mulSingle`, whose
other coordinates are identity matrices. Finally, `allIntegral` is the open
subgroup of families integral at every place.
`map_standardIntegral_restrictedProductEquiv` and
`image_standardIntegral_restrictedProductEquiv` give the subgroup and set image
identities. No compactness or nonzero-rank hypothesis is used in this comparison.
