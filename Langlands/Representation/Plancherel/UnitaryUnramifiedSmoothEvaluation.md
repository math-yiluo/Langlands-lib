# Smooth Laurent evaluation of unitary unramified characters

Worker 200. This internal coordinate and finite-family construction supplies a
prerequisite for translation on the existing compact model of orbit sections.
It reuses the published real-angle smoothness convention, integer torus
characters, and rational valuation-image coordinates.

`HasLaurentUnitaryCoordinates ν e` states an algebraic condition on a supplied
group equivalence from the actual unitary unramified characters to a finite
torus. For each group element `m`, evaluation of the character reconstructed
from `z` is an integer Laurent character of `z`. The exponents may depend on
`m`; they do not depend on `z`. A merely continuous equivalence is not treated
as sufficient for this condition.

`isSmoothFiniteTorusFunction_torusCharacter` uses the existing identity that
the real-angle lift of an integer torus character is the complex exponential
of a continuous real-linear form. This proves smoothness.
`unitaryUnramifiedSmoothEvaluation` then constructs actual evaluation as an
element of the existing scalar smooth-function algebra. Its value at `z` is
literally the value at `m` of the character `e.symm z`.

`mem_finiteSmoothFamilies_smul` proves closure of the existing finite
scalar-smooth family space under multiplication by a smooth scalar function.
The proof multiplies the scalar functions in a finite expansion and keeps the
constant coefficient vectors. No coefficient topology, norm or finite
dimension is used.

The rational theorem
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent`
discharges the condition for the published canonical coordinates of a
connected reductive group over a nonarchimedean local field. It uses exactly
the existing character reconstruction formula, with exponents given by the
integer basis coordinates of the actual valuation image of `g`. It imposes
no characteristic, splitness or quasisplitness restriction. The coordinates
carry the canonical rational-point topology already used in their definition.

The group, character-index, parameter and coefficient universes are
independent. This module constructs no induced action, wave packet,
intertwining continuation or Plancherel transform. It assumes no smooth
character-evaluation conclusion; the generic conclusion is derived from the
algebraic formula, and that formula is verified for the canonical rational
coordinates.
