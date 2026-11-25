# Pointed étale lifting of actual cocharacters

`HomScheme.pointedEtaleCocharacterLift` constructs a lift of any prescribed
residue-field cocharacter of a smooth affine group over an arbitrary scheme.
The returned `PointedEtaleCocharacterLiftData` records an étale neighbourhood,
a residue-valued point over the original point, an actual cocharacter over
the neighbourhood, and its exact recovery equation.

The recovery equation uses `Dynamic.baseChangeCocharacter` and the canonical
`Descent.pullbackComparison` for the residue point followed by the neighbourhood
projection. It thus compares actual cocharacters with the same multiplicative
source, including the equality between the composite base map and the canonical
residue map.

`cocharacterOfRelativeHom` normalizes a relative Hom family with source
`G_m` by precomposing with the inverse multiplicative base-change isomorphism.
`cocharacterOfRelativeHom_recovers` proves that exact relative Hom evaluation
is exact recovery of this normalized cocharacter. Its proof uses the
evaluation comparison and multiplicative pullback tower coherence, then cancels
the source isomorphisms.

The provenance is internal. The construction specializes the pointed split-torus
Hom lift to the multiplicative group, which is a split torus. It asserts no
local persistence of the dynamic parabolic defined by the lifted cocharacter.
