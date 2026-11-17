# Canonical face-filtration terms with a fixed torus

This derived unit removes the common-positive-base hypothesis from the
comparison of actual split parabolic face charts. The two charts have the
same ambient coordinate torus, fibrewise root datum and original coordinate
cocharacter, but may have different compatible positive bases, actual root
parametrization families, root enumerations and auxiliary regular cocharacters.
The commutative base ring is assumed nontrivial. Reductivity and actual
fibrewise torus maximality and root-datum data are retained.

`faceHeight_eq_of_sameCocharacter` proves equality of the two stored integral
face-height forms on the entire root span. The charts' coordinate-pairing
equations identify their coweight evaluations on every root. Dominance therefore
transfers to one common coweight. The actual root-datum Weyl-finiteness theorem
discharges the finite-reflection-group premise of the prescribed-dominant-base
comparison. The same-simple-zero-set comparison then handles any difference
between the two full-lattice coweights outside their root evaluations.

`isPos_of_coPairing_pos` shows that every strictly positive original root
pairing belongs to either compatible positive system. Its negative otherwise
has nonnegative dominant evaluation, a contradiction.
`weight_pos_iff_coPairing_pos` identifies the positive natural face weights
with the strictly positive original root pairings among the selected roots.

`range_inclusion_comp_le_of_height_eq` matches only roots active at cutoff
`d+1`, which is strictly positive. Such a root has positive original pairing,
so its label occurs in both charts. Exact face-height equality identifies its
unscaled weight, and actual root-parametrization certificates identify its
ambient root range. The generated-subgroup supremum then gives the range
inclusion on every scheme test. Matching only active roots permits the two
lists of zero roots to be different.

`range_inclusion_comp_sameTorus` applies that argument in both directions to
identify every actual ambient filtration term on all scheme tests.
`sameTorusTermIso` constructs the actual representing-group comparison at each
level; its companion equation preserves the exact ambient maps.

Provenance is the actual canonical face charts, prescribed-dominant-base
face-height equality, full Weyl finiteness for actual fibrewise root data,
dominant root signs, actual relative root-range certificates, and the ambient
generated-root description of represented terms. Changing the maximal torus,
changing the original cocharacter, and global descent are not asserted here.
