# Diagonal rescaling into the actual principal congruence subgroup

This internal construction uses a diagonal invertible matrix whose entries are
successive powers of a field unit. Conjugating by its inverse multiplies an
upper entry in position (i,j) by the (j-i)th power of that unit.

For a compact set of upper unitriangular matrices over a nonarchimedean local
field, all entries have a common valuative bound. Choosing the rescaling
parameter strictly smaller than the inverse of that bound puts every
non-diagonal entry strictly below one in valuation. Lower entries stay zero.

A separate bridge takes an actual invertible field matrix whose matrix and
inverse are integral and whose entrywise difference from the identity is
strictly small. It constructs its integral lift using both matrices and puts
the original rational point in the standard model's principal congruence
subgroup, using the actual maximal ideal of the canonical valuation ring.

The provenance is internal: compact entry bounds, diagonal conjugation,
the published integral matrix lifting criterion and the actual standard
congruence-point constructor. For a compact subgroup, the same rescaling also bounds the inverse matrices,
since the inverse remains in the subgroup. The diagonal entries remain one.
Thus `exists_rescale_mem_standardCongruence` places every rescaled group element,
read through the original rational matrix equivalence, in the actual standard
level-one congruence subgroup. The matrix group and its parameter may live in
independent universes.

This module supplies a focused input toward compact-unipotent pro-p arguments;
it makes no maximal subgroup assertion.
