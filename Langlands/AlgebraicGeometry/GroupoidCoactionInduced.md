# Coactions induced from the invariant ring

Author: Worker 1203.

This internal development for the Serre criterion proof extends an arbitrary
module `N` over `A = GroupoidCoaction.invariantRing t` to the `B`-module
`B ⊗[A] N`. Its coaction sends `b ⊗ n` to `t b ⊗ (1 ⊗ n)`.
The equality of the source and target maps on `A` makes the formula balanced.
The diagonal and cocycle identities follow by evaluating this formula at
the ring-valued points in the unchanged published `GroupoidCoaction`.
No flatness, acyclicity, or ring equivalence relation hypothesis is needed
for this construction.

The unit map `inducedUnit` sends `n` to `1 ⊗ n`, which is invariant.
Extension of scalars of a linear map is equivariant for these coactions,
and `inducedUnit_natural` expresses the naturality of the unit.

For a basis of `N` over `A`, its base change is a basis of `B ⊗[A] N`
over `B`. Applying each base-changed coordinate functional to the
invariance equation, and using the right-unit tensor equivalence, shows
that its coordinate `b` satisfies `t b = algebraMap B C b`. Thus every
coordinate of an invariant vector belongs to `A`. The finite coordinate
support then defines a vector over `A` whose image under the unit is the
given invariant. The same coordinate computation proves injectivity.
The lemmas `inducedUnit_injective_of_basis` and
`inducedUnit_surjective_of_basis` work with a supplied basis;
`inducedUnit_bijective` uses `Module.Free` to choose one. Ring and module
universes are independent, and a basis may have any index universe.

The construction is derived directly from the published definitions and
the equalizer-ring and invariant-module API in `GroupoidCoactionInvariants`,
with Mathlib tensor product and basis operations at the prepared Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. This is proof infrastructure
and does not prove the Serre criterion. In particular, bijectivity of the
unit for arbitrary modules is a remaining step which will use acyclicity.
