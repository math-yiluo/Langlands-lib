# Actual characteristic coefficients for Cartan invariant restriction

This internal construction projects the actual mixed archimedean matrix
algebra to a complex matrix at each real or complex place. At real places it
uses the ordinary real-to-complex inclusion. The real-linear projections extend
complex linearly to the actual complexified Lie algebra. Their matrix entries
are dual generators of the full Lie polynomial algebra.

The characteristic coefficients of these matrices over the polynomial algebra
evaluate to the characteristic coefficients of the actual evaluated matrices.
Actual group conjugation projects to similarity by an invertible matrix.
Characteristic polynomial invariance under similarity and real-point polynomial
separation prove invariance under the whole actual infinite adelic group.
The construction permits every natural rank, including zero.

`lieDiagonalPolynomialRestriction` composes the actual Cartan and diagonal
polynomial restrictions. `cartanDiagonalCoordinateDual` is the actual diagonal
entry functional pulled back from the full complex Lie space, and
`cartanDiagonalCoordinate` is its polynomial generator. Its pure-tensor formula
is the scalar times the chosen real diagonal coordinate. Tensor-product
extensionality proves that all off-diagonal entries restrict to zero and the
diagonal entries restrict to these generators.

Consequently `lieCharacteristicPolynomial_diagonal_restriction` identifies the
restricted polynomial as the product of `X - C(x_i)` for the actual diagonal
coordinate generators at that place. Taking coefficients gives
`lieCharacteristicCoefficient_diagonal_restriction`. Trace duality transports
each full-group invariant coefficient to the actual fixed symmetric algebra
as `lieCharacteristicSymmetricInvariant`. The final theorem identifies its
actual symmetric projection and compact-invariant diagonal restriction with the
same coefficient of that diagonal product.

The content is derived internally from the existing actual matrix and
polynomial definitions and Mathlib's characteristic-polynomial identities.
No external existence or invariant-theory assertion is assumed. Number-field
finiteness is used for real-point separation and trace duality in the
full-group invariance and invariant tensor results; the coordinate and diagonal
identities themselves work for an arbitrary field `K : Type u`. At a complex
place this construction uses the ordinary complex matrix projection; it does
not claim to separate both matrix factors of the full complexified real Lie
algebra. Its diagonal coordinates are real before complexification, so this
projection does retain every complementary diagonal entry.

Finite integral extension, actual invariant finiteness and enveloping central
generation are separate obligations.
