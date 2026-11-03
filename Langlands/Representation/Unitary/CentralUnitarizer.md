# Positive central unitarization through an abelian quotient

This internal construction takes a homomorphism `q : G →* A` from a
topological group to a commutative group. Its assumptions are that the kernel
of `q` is open, the kernel of its restriction to the actual full center is
compact, and that restriction has finite-index image in `A`. The target group
`A` needs no topology, and `q` need not be surjective. The group, quotient and
representation-carrier universes are independent.

For an actual scalar central character `χ` with open kernel,
`PositiveCharacter.normCharacter χ` is its nonnegative-real-unit modulus.
Its kernel contains the kernel of `χ`, so is open. The compact-subgroup
triviality theorem in `PositiveCharacterExtension` makes this modulus trivial
on the kernel of `q` restricted to the center. `normOnImage` therefore descends
the modulus to the actual central image by the universal property of a
surjective homomorphism. Its application lemma verifies the descent formula.

`centralUnitarizer` extends this descended character to `A` by the explicit
finite-index positive-root construction, pulls it back along `q`, and takes
its inverse. Its restriction to the center is exactly the inverse modulus of
`χ`. Its kernel contains the open kernel of `q`, proving that it is a smooth
positive character on `G`.

`unitaryCentralCharacter` constructs the existing `UnitaryCentralCharacter`
datum on the actual scalar twist of the original representation by the
complex embedding of `centralUnitarizer`. The resulting central character
is the product of the twisting character restricted to the center with `χ`.
The intersection of their open kernels proves smoothness. The inverse
modulus identity gives norm one, and the supplied scalar action of `χ`
gives the scalar action of the product on the unchanged carrier.

For an irreducible admissible complex representation,
`exists_positive_twist_unitaryCentralCharacter` obtains the actual central
character from the published `admissibleSchur_centralCharacter` and applies
this construction. No scalar-action premise or finite-dimensionality of the
whole representation is added to that result.

The proof uses positive real powers, compact discrete quotients, descent of
homomorphisms, scalar twisting and the published admissible Schur theorem.
It uses no Langlands classification, representation-character independence,
geometric lemma, adjointness or cuspidal-support theorem.

The compact central kernel, finite-index central image and open ambient
kernel remain explicit consumer obligations. This module does not establish
them for a rational reductive group, assert unitarizability of the entire
twisted representation, or prove rational rank-one Levi self-association.
