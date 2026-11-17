# Rectangular product majorants and their additive integral

This internal module defines `rectangleEntryEquiv F d a`, a continuous additive
isomorphism from `d × a` adelic matrices to `d*a` rank-one adelic rows. Its
coordinates use `finProdFinEquiv`, in precisely the same order as the rectangle
part of `rectangularJointRow`.

For every rank-one Schwartz–Bruhat function, the product of its norms at these
entries has finite lower integral for the actual `rectangleMeasure F d a`.
The result assumes the usual compact additive adelic quotient and includes zero
entries. The proof transports this measure along the entry isomorphism. The
published rectangular Haar theorem makes the transported measure an additive
Haar measure. Haar uniqueness compares it with the product of the rank-one
rectangle measures by a finite positive scalar. Finite product Tonelli then
reduces finiteness to rank-one Schwartz integrability, supplied by
`EqualAnalytic.schwartzBruhat_properties`. The empty finite product is handled
by the same theorem.

The module also proves `exists_normalized_rectangular_product_majorant`.
It applies the published product Schwartz-majorant theorem to the joint
Schwartz function constructed in `RectangularNormalizedMajorant`. Splitting
the joint row's finite product gives one product in the original leading roots
and another product in all rectangular entries. The same rank-one Schwartz
function bounds the normalized root-profile expression for every leading
diagonal, rectangle, and supplied standard-compact Iwasawa factorization.

These are derived analytic helpers, not a proof of the rectangular Mellin
statement. Connecting the normalized profile to a gauge and performing the
weighted torus and quotient integrations are separate steps.
