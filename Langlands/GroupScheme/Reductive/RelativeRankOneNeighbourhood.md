# Relative rank-one reductive good neighbourhoods

This internal construction assembles a relative rank-one step over an
arbitrary commutative ring. It imports the published proof
`rankOneWeylReductivity` of the exact `RankOneWeylReductivityStatement`;
no field-criterion proof is an input to this construction.

The supplied relative data are a closed standard split torus in a smooth
affine group scheme, a base point where that torus is self-centralizing
inside the actual geometric identity component, and a nonzero integral
character vector. At the specified fibre the actual root support in
integer coordinates must be exactly that vector and its negative, and
both actual weight spaces must be one-dimensional. These field-profile
hypotheses are explicit inputs, not consequences asserted from an
unproved reductive-group structure theorem.

One also supplies an integral coordinate automorphism inverting that
vector, an actual relative section satisfying the corresponding all-test
transporter equation, and the existing section-neighbourhood data that
place it in actual geometric identity components.

`rankOneIdentityComponentReductiveNeighbourhood` returns an actual open
neighbourhood of the original point contained in the actual reductive
geometric identity-component locus. The neighbourhood is the intersection
of a simultaneous root-profile neighbourhood, the open self-centralizing
torus locus, and the supplied section neighbourhood.

At each point of this intersection the integer-indexed actual roots and
all weight dimensions equal those at the original fibre. The field
character-coordinate equivalence converts this to exactly the two
actual character roots and their line dimensions. The torus is still
closed and self-centralizing. The section construction gives an actual
point in the actual geometric identity component, in the coefficient-point
convention of the field criterion, realizing the specified automorphism.
The integral inversion identity gives its actual character-inversion
equation. Applying the published field criterion proves connected
reductivity at that point.

The provenance is internal: this is a composition of actual root-profile
constancy, self-centralizer openness, the section/transporter comparisons,
integral character coordinates, and the proved field
criterion. No connectedness of the original fibres, noetherian hypothesis,
or characteristic restriction is imposed. Construction of the original
field profile and the relative transporter section, and the final general
openness assembly remain obligations.
