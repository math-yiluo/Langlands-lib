# Incident facets in prescribed cocharacter directions

This internal unit constructs an incident apartment facet for a prescribed
actual torus cocharacter, including cocharacters that vanish on some roots.
It combines the imported local finiteness, short-ray sign, integer-building
and incident-facet root-filtration theorems. No new external source assertion
is used.

For a locally finite reflection arrangement on a real affine torsor,
`exists_pos_isFaceOf_facet_smul_vadd` chooses a positive real parameter
along any direction. Nonzero root signs at the origin are preserved;
this puts the origin's entire facet in the formal closure of the new
facet. A root vanishing at the origin has the sign of its derivative on
the direction, because the parameter is positive.

For integer-valued building data `B`, `cocharacterDirection` is the class
of `1 tensor nu` in the reduced apartment's translation space.
`rootForm_cocharacterDirection` evaluates a relative root on this class
as the real image of its integer lattice pairing with `nu`.
`exists_pos_incidentFacet_of_cocharacter` applies the preceding ray
construction, using the actual building's locally finite arrangement.
For every root whose integer pairing is nonnegative, the displacement
has nonnegative root evaluation; the imported incident-facet comparison
then makes the two nonstrict root fixers equal. The sign assertion for
all affine roots vanishing at the origin is retained.

`HasPrescribedCocharacterIncidentFacets` records the existence of an
incident facet with these nonnegative-root fixer equalities for every
apartment point and every actual cocharacter. Its proved witness is
`hasPrescribedCocharacterIncidentFacets`. The underlying field has
arbitrary universe. This unit does not identify special-fibre images or
prove attainment of parabolic subgroup functors.
