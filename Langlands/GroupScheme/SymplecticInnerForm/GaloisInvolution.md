# Involutions on Galois-fixed algebras

Let `L/K` be a field extension and let `B` be an `L`-algebra with compatible
`K`-algebra structure. Given a `SemilinearGaloisAction ρ` and an `L`-linear
first-kind involution `τ` commuting with every action map, `fixedInvolution`
restricts `τ` to the `K`-subalgebra `ρ.fixed`. Commutation supplies fixedness
of the image. Linearity, the unit law, reversed multiplication and order two
are inherited from `τ`.

If `L/K` is finite Galois, `descentEquiv_fixedInvolution` proves that the
published algebra isomorphism `L ⊗[K] ρ.fixed ≃ₐ[L] B` intertwines the
scalar extension of this restricted involution and the original involution.
Tensor induction reduces the assertion to `l ⊗ a`, where it is the
`L`-linearity of `τ`.

This is a derived internal extension of the published
`SpecialLinearInnerForm.GaloisDescent` interface. It uses its actual fixed
subalgebra and multiplication isomorphism and introduces no existence claim
for an action, a matrix chart, or an inner-form presentation.
