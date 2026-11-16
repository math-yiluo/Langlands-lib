# Proper dynamic quotients of general linear groups by matrix methods

Worker 708. This internal result proves properness for every supplied separated
locally finite type dynamic quotient of `GL_N` over an algebraically closed
field in any universe. The projection is assumed surjective and constant on
right cosets of the dynamic subgroup on every relative scheme test.

The proof diagonalizes the given cocharacter by a matrix over the field.
Sorting its integer weights gives a permutation matrix whose conjugation
carries upper triangular matrices into its block parabolic. This follows
entry by entry on every test scheme: a prohibited entry has its row strictly
after its column in the sorted order and therefore vanishes. The block
parabolic equals the dynamic parabolic by the direct orbit calculation.
Transport back through the diagonalizing automorphism gives an automorphism
carrying the standard upper triangular subgroup into the original dynamic
subgroup.

The standard upper triangular subgroup is a Borel by the direct matrix
maximal-solvable proof in the Library. The paired Borel-coset properness lemma
applies to the composite of the automorphism and the supplied projection.
Its target is the same supplied quotient.

The construction `properDynamicQuotient` chooses an actual homogeneous
quotient by `Dynamic.Affine.parabolicHom χ`. That subgroup is closed by its
affine coordinate construction and smooth by the graded smooth algebra proof
of `dynamicSmooth`. Smooth subgroup quotient existence supplies the separated
locally finite type quasi-compact quotient, with smooth surjective
quasi-compact projection and exact right-coset fibers on every relative test
scheme. Its properness follows from the supplied-quotient theorem above.
No quotient properness assumption is used to construct it.

This route uses proper Borel quotients, Borel conjugacy, direct matrices and
weight decomposition. It does not use the general regular-cocharacter/Borel
theorem, parabolic recognition or the excluded rank-one results. It makes no
claim about dynamic quotients of general connected reductive groups.
