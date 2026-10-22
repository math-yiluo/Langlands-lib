# Algebra involutions and scalar extension

This module implements the algebra operation used to define Harris's unitary
groups. `AlgebraInvolution R A` is an actual `R`-linear map of the algebra `A`,
with certificates that it preserves the unit, reverses multiplication, and
squares to the identity. It is input algebraic data, not a supplied unitary group
or a conclusion about Shimura varieties.

The constructor `ofStar` reuses a Mathlib star structure when the base-ring
star is trivial. `units` constructs its action on actual invertible elements.
`inverseUnits` composes it with inversion to give a multiplicative equivalence.
Their certificates follow from reversal of multiplication and involutivity.

`baseChange` constructs the involution on the actual tensor product
`S ⊗[R] A`. It acts by `s ⊗ a ↦ s ⊗ σ(a)` and fixes the coefficient algebra
`S`. In particular, base change to the complex numbers does **not** conjugate
that new coefficient factor. The multiplication and involutivity certificates
are proved by tensor-product induction. `changeCoefficients` is Mathlib's tensor
product of the coefficient homomorphism and the identity on `A`. The file proves
its compatibility with the involution and scalar embedding, and its identity
and composition laws.

All carrier universes are independent. The base ring and coefficient algebras
are commutative rings; `A` is an associative unital, potentially noncommutative
algebra. No field, dimension, or nontriviality assumption is used here.

Source correspondence: Michael Harris, *Galois properties of cohomological
automorphic forms on GL(n)* (1999), Section 1, printed page 301, defines the
second-kind involution on a central simple CM-field algebra and uses its unitary
and rational-similitude equations. Robert Kottwitz, *On the λ-adic representations
associated to some simple Shimura varieties* (1992), Section 1, page 654,
explicitly uses the scalar extension to every commutative rational algebra.
This module supplies the elementary algebra mechanism for those equations;
the CM center, second-kind condition, and signatures belong to the specialization.
It asserts neither representability nor a canonical model.

Implementation dependencies are the pinned Mathlib tensor-product algebra,
linear base change, units, and multiplicative equivalence interfaces. This is
original implementation by Worker 57. Compilation and independent publication
status are recorded separately from this mathematical description.

Exact retained sources: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; `kottwitz-1992-lambda-adic-simple-shimura`, SHA256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`. The locators above refer to these files. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435` with Lean `4.34.0`.
