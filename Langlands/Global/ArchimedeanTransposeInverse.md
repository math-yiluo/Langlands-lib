# Transpose inverse on the actual archimedean algebras

This is an internal algebraic construction for
`CuspidalTransposeInverseContragredientStatement`. Its
purpose is to supply the algebra maps used in the transpose-inverse twist of an
actual automorphic operator realization. It is derived directly from the
published concrete matrix Lie algebra and Mathlib's scalar extension and
universal enveloping algebra; no representation-theoretic result is assumed.

For every field `F` in an arbitrary universe and every natural number `n`,
`realLieIota F n` is the real Lie algebra automorphism
`X ↦ -Xᵗ` on `RealLieAlgebra F n`. The matrix coordinates take values in the
mixed archimedean space of `F`. The bracket calculation uses
`(XY)ᵗ = YᵗXᵗ`, and applying negative transpose twice is the identity.
The construction requires no number-field hypothesis.

`complexLieIota F n` is its complex-linear scalar extension; on pure tensors
it sends `z ⊗ X` to `z ⊗ (-Xᵗ)`, fixing the complex coefficient. Tensor-product
induction proves that it is involutive.

`envelopingIota F n` is the induced complex algebra automorphism of the actual
universal enveloping algebra. Its value on a Lie generator is the generator
of `complexLieIota F n X`. The universal property, checked on generators,
proves that its square is the identity. Finally, `centerIota F n` restricts
this automorphism to the genuine algebra center. Surjectivity of the
enveloping algebra automorphism gives preservation of the center; the
restriction is involutive and commutes with the center inclusion.

These definitions and identities describe the expected differential
automorphisms for `g ↦ (g⁻¹)ᵗ`. This module does not identify them with
derivatives of that group map, construct a twisted automorphic realization,
or prove a Gelfand–Kazhdan or contragredient theorem.
