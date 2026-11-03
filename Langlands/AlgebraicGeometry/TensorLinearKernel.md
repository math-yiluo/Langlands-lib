# Finite linear equations for kernels after tensoring finite free modules

Let `R` be a commutative ring, let `f : P →ₗ[R] Q` be an actual module map,
and choose finite coordinate isomorphisms
`eP : P ≃ₗ[R] (Fin n → R)` and `eQ : Q ≃ₗ[R] (Fin m → R)`.
`FiniteLinearEquations.TensorKernel.matrix f eP eQ` is the matrix of this
map in those coordinates.

`coordinates eP A` identifies the ordinary tensor product `A ⊗[R] P`
with `Fin n → A`, for any `R`-module `A`. The implemented construction
first tensors the coordinate isomorphism and then distributes the tensor
over the finite product. `coordinates_map` proves that tensoring `f` acts
by its matrix, using pure tensors and additivity.

For every commutative `R`-algebra `S`, `kernelEquiv f eP eQ S` identifies
the actual linear kernel of `id_S ⊗ f` with
`FiniteLinearEquations.Solutions (matrix f eP eQ) S`. The equations use
the given algebra map `R → S`. `mapKernel` is induced by tensoring a
coefficient-linear map on the left, and `kernelEquiv_naturality` proves
compatibility with every scalar-compatible algebra map `S → S'`.
The result includes arbitrary coefficient algebras and zero ranks.

This is an internal algebraic construction for the finite-matrix step in
proper module Hom. Its inputs are an actual map and chosen finite free
coordinates; it asserts no existence of those inputs, no comparison with
geometric Hom, and no local covering theorem. The proof uses Mathlib's
finite-product tensor coordinates and matrix of a linear map. No
flatness assumption on `S` is needed.
