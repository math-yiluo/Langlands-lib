# Ambient central unitarization of actual normalized induction

This internal construction starts with an actual closed-radical semidirect
decomposition `P = M ⋉ U` in a locally compact nonarchimedean group `G`.
The full abstract ambient center is contained in `M`. An inducing
representation has a specified scalar central character with open kernel.

The structural inputs to the central extension construction remain explicit:
an abelian quotient homomorphism `q`, openness of its ambient kernel,
compactness of its restriction kernel on the full abstract center, and finite
index of that center's actual image. The ambient group, quotient and
representation carrier universes are independent.

`inductionCentralUnitarizingCharacter` first restricts the given Levi scalar
character to the ambient center, then applies the existing
`CentralUnitarization.centralUnitarizer`. This produces an actual positive
character on `G` that cancels the modulus of that inherited character.
`positiveSmoothCharacter` converts it to a complex smooth character.
`centralUnitarizedInduction` induces the original Levi representation after
twisting by the restriction of this ambient character.

If `U` is a limit of compact subgroups, the positive character kills `U`.
The existing character-multiplication comparison on actual induced functions
then gives `centralUnitarizedInductionEquiv`. The generic central-unitarizer
construction supplies a unitary scalar action on the ambient twist of the
original induction. Pulling that datum through the displayed equivalence
gives `centralUnitarizedInductionUnitaryCentralCharacter` on the actual
induction of the twisted Levi representation. `UnitaryCentralCharacter.pullbackEquiv`
is the elementary transport used here; it retains the same scalar character.

`centralUnitarizedInduction_isIrreducible_iff` applies the existing normalized
induction character-twist comparison and scalar-twist irreducibility theorem.
Consequently reducibility is preserved. The separate
`isCorollaryLeviCuspidal_positiveAmbientTwist_iff` applies the existing exact
inside-Levi cuspidality transport to an arbitrary positive ambient open-kernel
character. Compact limits of all standard radicals discharge its character
triviality requirements, including those in the literal subgroup copies inside
the Levi.

These are derived constructions from the actual subgroup, induced-function,
scalar-twist and central-character definitions. They do not assert the
structural inputs for a rational reductive group, admissibility or the existence
of a scalar central character for an arbitrary inducing representation, a
positive invariant form on the whole induction, any exponent bound,
square-integrability criterion or the self-association theorem.
