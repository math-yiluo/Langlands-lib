# Extending actual adic conjugators by one level

This internal reduction implements the conjugator recursion in the proof of
SGA 3, Exposé IX, Corollaire 7.3 (Gille–Polo recomposed edition, 2009,
p.59, original margin p.72; source `sga3-expose-ix-gille-polo-2009`).
The infinitesimal proposition remains an explicit mathematical input.

`PointTopology.surjective_changeRing_of_nilpotent_surjection` lifts actual
points of any smooth affine scheme through a surjective algebra map with
nilpotent kernel. It passes to the actual affine coordinate algebra, uses
formal smoothness to lift the algebra homomorphism, and converts back to
scheme points with the prescribed reduction.

`restrict_projected_point_eq_one` checks that a base point of a pullback
group whose restriction is the identity projects to a test-valued point
with identity restriction. It uses the published point adjunction and the
canonical isomorphism of the underlying test schemes.

`Adic.transitionAlgHom` expresses a successive adic quotient map as an
algebra homomorphism over the original ring.
`Adic.point_step_surjective` applies the point-lifting theorem to its
square-zero kernel.

For a multiplicative-type group `H` and smooth affine group `G` over
`Spec A`, `Adic.conjugator_step_of_infinitesimal` extends a conjugating
point at level `n` to level `n+1`, assuming
`MultiplicativeTypeInfinitesimalLiftStatement`. It first lifts the point
using smoothness. The conjugated and desired homomorphisms then have equal
restrictions at level `n`; the infinitesimal theorem supplies a correcting
point reducing to the identity. Multiplying this correction by the lifted
point preserves its reduction and gives the required conjugacy at the next
level. The order of the product follows the Library identity
`innerIso_mul_hom`.

`Adic.conjugacy_of_infinitesimal_and_injective` combines this step with
dependent recursion and affine point algebraization. Under
`IsAdicComplete I A`, and assuming injectivity of the actual adic Hom
restriction map, two global homomorphisms with equal level-zero
restrictions are conjugate by a global point reducing to the identity.
No noetherianity or isotriviality is used in this conditional reduction;
these enter the adic Hom-injectivity input.
