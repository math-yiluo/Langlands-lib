# Tensor coefficients for regular module representations

This internal construction extends the natural module representations of
`RegularCochains` by an arbitrary base module with the trivial action. Let `R`
be a commutative ring, `H` a group scheme over `Spec R`, and `M`, `N` arbitrary
`R`-modules. No flatness, finite generation or freeness is assumed for either
module.

`coefficientTensorAssoc` is the canonical test-algebra-linear reassociation
`(A ⊗[R] M) ⊗[R] N ≃ A ⊗[R] (M ⊗[R] N)`. The element construction
`tensorCoefficientPoint` and its naturality lemma identify the reassociated
pure tensors under every morphism of test algebras.

`ModuleRepresentation.tensorTrivial` extends the given action on `A ⊗[R] M`
by the identity on `N`, conjugating the resulting tensor automorphism through
this reassociation. The proof checks the monoid laws using the tensor congruence
laws and proves naturality by tensor induction, reducing to naturality of the
original representation. `tensorAction_point` gives its action on an extended
module point tensored with a constant element of `N`.

This is derived tensor algebra for the project's regular-cochain interface. It
asserts no comparison with pointwise reduction kernels.
