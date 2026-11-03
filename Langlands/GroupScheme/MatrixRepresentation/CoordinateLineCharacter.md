# The character of a stabilized coordinate line

This internal construction starts from an actual finite matrix representation
of a group scheme over an arbitrary commutative ring. The hypothesis
`StabilizesCoordinateLine` says that every scheme-test point multiplies the
chosen coordinate vector by a global unit.

The unit is unique because its value is the chosen diagonal matrix entry.
`coordinateLineScalar` chooses it; its defining action equation and entry
formula show that it is multiplicative and commutes with pullback on every
scheme test. Combining this natural homomorphism with the published
`Gm.pointsEquiv` and `homOfPoints` constructs the actual rational character
`coordinateLineRationalCharacter`. Its evaluation is the chosen unit, and
`coordinateLineCharacter_action` recovers the original matrix action on the
coordinate vector.

The construction uses only the published matrix-coefficient, multiplicative
group and Yoneda interfaces and elementary matrix identities from Mathlib.
No smoothness, reducedness, connectedness or field hypothesis is required.
An intended consumer is the action on the Chevalley line for a closed
normalizer. This module does not construct that normalizer, establish
surjectivity of a torus commutator, or prove Borel self-normalization.

`StabilizesCoordinateLine` reuses the published `PreservesCoordinateLine`
predicate, and the scalar and point homomorphisms reuse
`Chevalley/UnipotentLine`. The additive rational character is the same
scheme character packaged by `Additive.ofMul`; the existing hom-valued
`coordinateLineCharacter` keeps its original type.
