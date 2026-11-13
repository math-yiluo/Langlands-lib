# Commuting lifts through finite-kernel homomorphisms

This internal construction extends the published finite-target rigidity argument
to arbitrary fields and applies it to commutators of two homomorphisms.

`finiteTargetOverHom_eq_one` states that a morphism from the underlying scheme of
a smooth connected affine group over a field to a finite group scheme is the
constant identity map if it sends the identity to the identity. The morphism is
not required to be a homomorphism. The proof changes base to an algebraic closure,
uses the published connected-reduced finite-target rigidity theorem there, and
reflects equality through the faithfully flat base change.

`commute_of_finiteKernel` takes a homomorphism `q : H ⟶ G` with finite
scheme-theoretic kernel and homomorphisms `a : C ⟶ H`, `b : D ⟶ H` from connected
reductive groups. If their composites with `q` commute on every relative test
scheme, their images in `H` commute on every relative test scheme. The proof
factors the actual two-input commutator morphism through the full kernel of `q`.
The source product is smooth, connected, and affine by the existing geometric
integrality theorem. The finite-target result makes the commutator the identity.
The argument permits nonreduced finite kernels and unrestricted characteristic.

`finiteKernelCommutingProduct` constructs the associated actual homomorphism
`C × D ⟶ H` from these same data. The lifted all-test commutation allows the
existing `commutingSubgroupMultiplicationHom` construction to combine `a` and `b`.
Its point formula `finiteKernelCommutingProduct_points` sends a pair `(x,y)` to
`a(x) b(y)` on every relative test scheme.

The provenance is internal: the finite-target result over an algebraically closed
field, geometric connectedness under field extensions, smooth geometric
integrality of products, actual scheme-theoretic kernels, and the commutator
morphism are imported Library constructions. No external-source correspondence
is claimed.
