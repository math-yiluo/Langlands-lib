# Prescribed scalar characters and compact quotient unitarity

Author: Worker 1597.

This is derived infrastructure for the proof of
`NormalizedTemperedCentralCharacterStatement`. Its provenance is internal:
it combines the published open-subgroup definition of smoothness and
`SmoothRep.HasCentralCharacter` with the ordinary group quotient and the
extreme value theorem in Mathlib. It asserts no additional theorem from
Renard and does not complete the tempered central-character target.

For a representation over any field, a prescribed scalar character along
a continuous homomorphism has open kernel if the representation is
nonzero and smooth. Choose a nonzero vector and an open subgroup fixing
it. The inverse image of that subgroup is open and lies in the character
kernel, because scalar multiplication on a nonzero vector detects
equality of scalars. A subgroup containing an open subgroup is open.
Translates of the kernel then give local constancy. The specialization
to `SmoothRep.HasCentralCharacter` uses the continuous inclusion of the
full group center. It requires neither irreducibility, admissibility nor
a topology on the representation carrier. The field, group, intermediate
group and carrier universes are independent.

`complexCharacterNorm` is the homomorphism sending a complex character
value to its real norm. `norm_eq_one_of_compact_quotient` takes a
continuous complex character, a normal subgroup on which its norm is
one, and compactness of the actual group quotient with its quotient
topology. The norm homomorphism descends to that quotient, and its
continuity follows from the quotient-map criterion. It attains a positive
maximum `M`. Evaluating at the square of a maximizing point gives
`M² ≤ M`, hence `M ≤ 1`. Thus every character value has norm at most one;
applying the same bound to the inverse gives the reverse inequality.

The compactness hypothesis is explicit. This module does not prove
compactness of the center modulo a split component, identify the scheme
center with the point-group center, or compare the identity Jacquet
module with the original representation. Those actual-group steps
remain necessary for the unchanged final target, as does the separate
normalized exponent unitarity theorem.
