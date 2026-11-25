# Shapiro comparison for coefficient tensor units

Let `B/F` be a finite separable field extension and let `L/F` be finite
normal with a specified embedding of `B` over `F`. All the fields lie in
the same universe. The group `Gal(L/F)` acts on the units of `B ⊗[F] L`
through the right tensor factor. `tensorUnitRepresentation` uses the
additive notation for that unit group over the lifted integers.

The tensor algebra splits by the embeddings `j : B →ₐ[F] L`. A pure
tensor `b ⊗ x` has coordinate `x * j(b)`. At `j`, a coefficient
automorphism `σ` applies `σ` to the previous coordinate at `σ⁻¹ ∘ j`.
This formula follows on pure tensors and extends by additivity. It
makes evaluation at the specified inclusion a morphism of coefficient
representations after restricting to `Gal(L/B)`.

The adjoint morphism sends a tensor unit to the function giving this
inclusion coordinate on each of its translates. Every embedding of
`B` extends to an automorphism of the normal field `L`, so these values
determine all coordinates. To obtain a preimage of a coinduced function,
insert a unit at the inclusion coordinate with all other coordinates
one, then take the coset sum in additive notation. The coordinate
formula verifies that this is a section of the adjoint morphism.

The resulting coefficient isomorphism and Shapiro give
`TensorUnitShapiro.cohomologyIso` in every degree. Its forward map is
restriction of cochains to `Gal(L/B)` followed by evaluation at the
specified inclusion. This internal comparison is used for the
Weil-restricted unit terms in the cohomology of norm-kernel centers.
