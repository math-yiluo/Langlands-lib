# Opposite factors for commuting cocharacters

`exists_lift_contraction_stableOpen` works over a field and on every test
scheme. Consider the residue field at a point of the test affine line.
The specialized orbit extension maps zero to the identity and hence maps
the generic point of the affine line into the given stable open. The
generic point comes from the Laurent chart. There the extension is the
conjugation orbit, so stability under both a unit and its inverse puts
the original specialized point in the open. The value of the extension
at the original residue-field coordinate lies there too, by stability
when the coordinate is a unit and by the identity-limit property when
it is zero. The open immersion then lifts the entire extension.

`exists_factors_unipotent_opposite_of_centralizer_le` applies this result
to the opposite open product of the second cocharacter. It lifts the
contraction of the inverse of a point in the first radical through
that product. The two factors are normalized by the first cocharacter
because both cocharacters go through the same commutative group scheme.
Injective multiplication makes the two factors contract along the
first cocharacter. The assumed centralizer inclusion makes the
parabolic factor contract along the second cocharacter as well.
Inverting the product places the common radical factor first and the
opposite radical factor second.

This is an internal consequence of the Library's opposite-cell theorem
`oppositeCellStatement`, its normalized product-contraction lemmas,
and `mem_unipotent_of_mem_unipotent_of_mem_parabolic`.
