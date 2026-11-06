# The normalized weight-one infinity character

This internal construction is used for the exact proposition
`Langlands.Global.CMHalfWeightCharacterStatement`. Its normalization is the one
in Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), proof of Corollary VII.2.8, printed pages 244–245: divide the algebraic
infinity character of pure weight one by the product of ordinary complex
absolute values, one for each infinite place. The module proves only the
archimedean formulas, and does not assert existence of a global Hecke character.

`absoluteValue` maps a complex unit to its norm, embedded back in the complex
units. `normalizedComplexCharacter p q` is `z^p conjugate(z)^q / |z|`.
The identity `z conjugate(z) = |z|²`, together with `p + q = 1`, shows that
conjugating the argument inverts this character. On a real argument the same
sum of exponents reduces its value to `z / |z|`.

`normCharacter` is the finite product of the coordinate absolute values on
actual archimedean ideles. `normalizedCharacter` is the quotient of the existing
`InfinityType.toCharacter` by `normCharacter`. The twist equation has precisely
the coercions and product used in the target. The local conjugation and real
formulas pass through finite products. The arithmetic conjugation formula
uses the published comparison with coordinatewise complex conjugation.

These are direct algebraic consequences of the existing infinity-character
construction; no global class-field or extension assertion is assumed here.
