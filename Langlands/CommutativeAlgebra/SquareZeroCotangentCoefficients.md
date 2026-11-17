# Quotient-base coefficients for a square-zero ideal

Let `R` be a commutative ring and `I` an ideal with `I² = 0`.
`idealCotangentEquiv` identifies the original `R`-module `I` with its canonical
cotangent quotient `I.Cotangent = I/I²`. The kernel formula for
`I.toCotangent` and its surjectivity prove bijectivity. The cotangent quotient
has its existing canonical `R/I`-module structure; no chosen lifts of quotient
scalars are introduced.

For any `R`-module `L` and any `R`-algebra `B`, `reducedCoefficientEquiv` is a
`B`-linear equivalence

`((R/I) ⊗[R] B) ⊗[R/I] (I.Cotangent ⊗[R] L) ≃ B ⊗[R] (I ⊗[R] L)`.

The first step uses the published generic
`ElementaryKernelTensor.coefficientTensorEquiv`. The second tensors the
inverse of `idealCotangentEquiv` with the identity of `L`. The displayed
left-hand side carries the `B`-action through the right factor of the actual
base-changed algebra.

The pure-tensor formulas identify `(1 ⊗ b) ⊗ (toCotangent(i) ⊗ x)` with
`b ⊗ (i ⊗ x)` in both directions. `quotientTestMap` is the actual
base extension of an algebra morphism, and `reducedCoefficientEquiv_naturality`
proves that the comparison commutes with every such morphism. Tensor induction
on the coefficient and algebra tensors reduces the proof to the published
pure-tensor formula and tensor-map functoriality.

This is internal derived tensor algebra. Neither `B` nor `L` is assumed flat,
finite or projective. No group action or geometric deformation assertion is
part of this generic comparison.
