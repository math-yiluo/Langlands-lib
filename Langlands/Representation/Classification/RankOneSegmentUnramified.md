# Unramified rank-one segment fixed vectors and decreasing heads

This internal unit applies the proved midpoint character formula to every
irreducible subrepresentation of an increasing rank-one segment whose base
acts by an unramified scalar character. Here unramified means trivial on the
actual field valuation units; all compatible topological realizations and
independent carrier and field universes are retained.

The midpoint determinant-power character and the unramified determinant
character are both trivial when the determinant has normalized norm one.
The scalar action formula therefore says that this entire subgroup fixes
every vector. The actual integral matrix subgroup lies inside it, since both
the determinant and its inverse have normalized norm at most one. Its fixed
space is the whole carrier and is nonzero by irreducibility.

The construction `unramifiedRankOneSegmentSocle` chooses the strong segment
socle supplied by the published segment existence theorem. It retains the
norm-one fixed-space equality and the strong head relation for the actual
decreasing segment induction. These are supporting constructions and lemmas;
they do not assert the full ordered spherical-generation theorem.
