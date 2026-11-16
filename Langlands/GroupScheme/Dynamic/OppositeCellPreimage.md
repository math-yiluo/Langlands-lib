# Pulling dynamic cell factors back through closed subgroups

This is an internal consequence of the published affine linear embedding,
diagonal cocharacter, matrix stabilizer, and dynamic limit interfaces. It
packages those results for an arbitrary closed subgroup of an affine group of
finite type over a field. It asserts no separate translation of a literature
statement.

Let `k` be any field, let `f : H → G` be a closed immersion of group schemes
over `Spec k`, assume that `G` is affine and locally of finite type, and let
`χ : Gm → H` be a cocharacter. No smoothness or connectedness is assumed.
All assertions hold in every universe and on every test scheme `T` over
`Spec k`.

`exists_opposite_factors_of_isClosedSubgroup` says that if a point `g` of `H`
has image `m * p`, where `m` belongs to `U_G(-(χ ≫ f))` and `p` belongs to
`P_G(χ ≫ f)`, then both factors lift to points `m₀` and `p₀` of `H`.
The lifts belong to `U_H(-χ)` and `P_H(χ)`, have the prescribed images, and
satisfy `m₀ * p₀ = g`. Here `-χ` means precomposition by inversion on `Gm`,
exactly as in the Lean expressions.

`oppositeFactorLift` chooses such a pair. Its subtype records the two
membership conditions, the two image identities, and the product identity.

`exists_triple_factors_of_isClosedSubgroup` gives the corresponding result
for an image decomposition `m * (z * v)`, with factors in
`U_G(-(χ ≫ f))`, `Z_G(χ ≫ f)`, and `U_G(χ ≫ f)`. It lifts all three factors
to the respective dynamic functors of `H`, with their prescribed images and
the same product `g`.

For the opposite-factor proof, a closed linear embedding of `G` is conjugated
so that the target cocharacter is diagonal. Composing with `f` gives a closed
linear embedding of `H`. Functoriality puts the matrices of `m` and `p` in
the negative block unipotent and block parabolic subgroups. Their product is
a zero of the equations defining `H`. The published matrix stabilizer
argument therefore makes the matrix of `p` a zero of those equations.
The closed-embedding lifting criterion supplies `p₀`. Cancellation against
the faithful target embedding identifies its image with `p`. The
closed-subgroup inverse-image criterion gives its parabolic membership.
Setting `m₀ = g * p₀⁻¹` gives the other factor and its dynamic membership.

For the triple-factor proof, first combine `z * v` into a parabolic point
and apply the opposite-factor result. The limit of its lift `p₀` is a
centralizer point `z₀`; the point `z₀⁻¹ * p₀` is unipotent. Naturality and
uniqueness of the dynamic limit identify their images with `z` and `v`.
Separatedness needed for these limits follows from the affine target and
the closed immersion.

This module treats ambient closed immersions over a field. It does not prove
the cell inverse-image statement for arbitrary-base monomorphisms, the
centralizer or torus closedness step, or the reductive monomorphism theorem.
