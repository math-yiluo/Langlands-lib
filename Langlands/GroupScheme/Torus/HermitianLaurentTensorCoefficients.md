# Actual tensor coefficients in Hermitian Laurent coordinates

This internal helper identifies the tensor coefficient algebra on the actual
affine test scheme of `K[M]` with `L[M]`. Here `K` and `L` are fields in a common
arbitrary universe, `L` is a `K`-algebra, and `M` is any additive commutative
monoid in that universe. When `M` is a finite free abelian group, these are the
Laurent coordinate rings needed for a split torus. The matrix index has an
independent arbitrary universe; it is assumed finite only for the Gram
preservation equation involving matrix multiplication.

`monoidAlgebraTest K M` is the relative spectrum of `K[M]`.
`tensorCoefficients K L M` first applies the existing
`FiniteAlgebraUnits.WeilMatrixPoints.affineCoefficientEquiv` to its actual
relative global sections. This tensors `Corepresented.affineSectionsAlgEquiv`
with the identity of `L`, giving `L ⊗[K] K[M]`.
Mathlib's `AddMonoidAlgebra.scalarTensorEquiv` then gives `L[M]`. The result is
recorded as an equivalence of `K`-algebras whose source is the raw tensor
product with actual sections. This is the underlying ring of
`SpecialLinear.WeilRoot.tensorAlgebra` at this test. `tensorCoefficients_tmul` specifies
its value on a pure tensor. `tensorCoefficients_algebraMap` identifies each
element of `L` with its constant monomial.

For a separable quadratic extension `L/K`, `tensorCoefficients_bar` identifies
the actual tensor involution with the coefficientwise field involution of
`HermitianLaurentOrthogonality`. It fixes all monomial exponents. The proof
inducts on tensors. On a pure tensor, the affine section factor is unchanged
and coefficient comparison reduces the identity to conjugation fixing the
image of `K`. The additive induction step follows from the ring
homomorphism laws. There
is no restriction on the characteristic or cardinality of either field.

`tensorCoefficients_gram` sends scalar extension of any original field matrix
to its constant Laurent matrix. `tensorCoefficients_preservesGram` applies
this coefficient equivalence to the entire conjugate-transpose Gram
preservation equation. Entrywise conjugation compatibility and constant Gram
compatibility give the same full matrix equation over `L[M]`. No Hermitian
symmetry or invertibility of the supplied matrix is needed for this transport.

The constructions are derived from the published affine section comparison
and tensor coefficient definitions, Mathlib's scalar extension equivalence,
and the coefficientwise involution. This module does not assert that a
particular group-scheme morphism preserves a Gram form; it transfers such an
equation when supplied. It does not prove a split-rank bound.
