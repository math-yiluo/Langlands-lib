# Extending a scalar character to the full point-group center

Author: Worker 1597.

This internal derived module specializes the compact-quotient norm argument
to the actual full center of a connected reductive group over a
nonarchimedean local field. It uses the published equality between scheme-center
points and the abstract center of the rational-point group. It introduces no
additional literature assertion. The generic character regularity and
compact-quotient argument are supplied by `Category/CentralCharacterRegularity`.

The input is a prescribed scalar central character of a nonzero smooth
complex representation. No smoothness or continuity of this character is
assumed: the scalar-action regularity theorem proves its open kernel and
local constancy from smoothness of the representation and a nonzero vector.
The rational-point group has its canonical evaluation topology, which makes
it a topological group. The vector-space carrier has no topology and its
universe is independent of that of the field and group scheme.

The character is pulled back along the canonical inclusion of full
scheme-center points into the abstract point-group center. This inclusion
is continuous for the inherited subgroup topologies. The denominator is
precisely the actual rational-point image of the supplied split component.
The assumed norm-one property on that split component gives norm one on
the denominator. With the explicitly assumed `CenterSplitComponentCompactness`
for the selected canonical quotient topology, the generic compact-quotient
norm theorem gives norm one on all scheme-center points. The published
`rationalCenterComparison` equality then covers every point in the full
abstract center.

`unitaryCentralCharacterOfSplitComponent` packages this norm conclusion,
the derived open kernel and the original scalar action in an actual
`UnitaryCentralCharacter` datum with the same prescribed character.

This module retains compactness and unit modulus on the split component
as explicit premises. It does not prove the unconditional compactness
statement, the identity-Jacquet comparison, or the normalized-tempered
central-character target. It imposes no characteristic, splitness,
irreducibility, admissibility or finite-dimensionality restriction.
