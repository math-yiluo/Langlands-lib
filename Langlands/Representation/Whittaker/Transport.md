# Pullback of Whittaker functionals

This is an internal algebraic construction derived from the published
`Langlands.Whittaker.functionals` definition and actual representation
intertwiners. It asserts no existence theorem for Whittaker functionals.

`functionalsComap f` sends a character-equivariant linear functional `ℓ` to
`ℓ ∘ f`. The subgroup and its character are unchanged. The intertwining
identity for `f` proves character equivariance; precomposition is linear.
The coefficient ring is any commutative ring, and the group and the two
representation carriers have independent universes.

`HasFunctional.of_surjective` proves preservation of nonzeroness under this
pullback when `f` is surjective. If the pullback vanished, every vector in the
target has a preimage, so the original functional would vanish. Applying this
argument to an equivalence and its inverse gives
`hasFunctional_iff_of_equiv`.

For the actual general linear group and its standard character,
`isGeneric_iff_of_equiv` combines that equivalence with the published
irreducibility and admissibility transport theorems. It preserves all three
clauses of `Whittaker.IsGeneric`: irreducibility, admissibility, and existence
of an actual nonzero functional. It permits different carrier universes and
does not require a topology on either representation module.

The construction uses only the published algebraic definitions and elementary
composition. Its provenance is internal; no additional literature theorem or
analytic classification result is used.
