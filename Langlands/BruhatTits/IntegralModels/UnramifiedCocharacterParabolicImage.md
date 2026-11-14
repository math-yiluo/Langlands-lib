# Prescribed residue cocharacters in actual incident comparison images

This internal composition uses the actual integral split torus in a supplied
smooth unramified zero-fixer model N, whose full special fibre is connected.
The base is the fixed-field integer ring of a nonarchimedean local field F;
C supplies the maximal-unramified building and E its zero datum. The nonempty
apartment subset Ω characterizes N's generic integral-point subgroup as
E.zeroPoints intersected with the fixer of its apartment image. All objects
have arbitrary universe `u`.

For any cocharacter ν of that actual residue torus, assume the target root
fixer on Ω is contained in the source root fixer on Ω' for every generic root
whose actual specialized pairing with ν is nonnegative, including zero.
Supply an actual source zero-fixer model M and generic-identity morphism
φ from M to N. The theorem
`unramifiedCocharacterDynamicParabolic_le_image_of_rootFixers_le` contains the
whole dynamic parabolic of ν in the actual closed schematic image of
φ's special-fibre map, on every residue-scheme test. M need not be smooth.

The actual full residue-root comparison lifts every residue root back through
the same integral torus. Its integral root model maps into M by the assumed
fixer inclusion, and generic rigidity identifies its composite with the
original target inclusion. Thus every nonnegative residue-root functor lies
in the image. The full torus centralizer lies in that image by the published
centralizer lifting theorem. Closed nonnegative-root generation supplies the
dynamic parabolic containment. This does not assume genericity of ν.

`exists_pos_incidentFacet_dynamicParabolic_le_images` starts with Ω contained
in the apartment facet of x. For every prescribed ν, a sufficiently short
positive ray in the direction of its actual generic lift selects an incident
facet. The prescribed-cocharacter ray theorem gives equality of nonnegative
root fixers on the two full facets. The published constancy on nonempty
subsets of a facet supplies the preceding containment for every source model
on any nonempty portion Ω' of the selected facet and every actual comparison
morphism into N. The theorem retains the positive parameter and the specified
cocharacter direction, rather than choosing an unrelated cocharacter.

`HasPrescribedCocharacterIncidentParabolicContainment` packages that positive-ray
and universal comparison-image conclusion as a proposition;
`hasPrescribedCocharacterIncidentParabolicContainment` proves it under the
smoothness and connected-special-fibre assumptions on N.

The result is a one-way containment. It does not assert equality with the
image, full unipotent-radical containment, parabolicity of the image,
attainment of every reductive-quotient parabolic, or the descended order
bijection. Its provenance is the imported Library constructions and proofs;
no new original-literature assertion is made.
