# Compatible-point maps and open charts

Author: Worker 105. Derived construction supporting the fibre-product gluing
argument in Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1, printed page 4.

`schemeCompatiblePairMap` sends an actual pair of relative S-points in a small
diagram to their postcompositions in a larger diagram. The two specified squares
commute, so compatibility is preserved. If the common target map is monic,
`schemeCompatiblePair_iff` proves that compatibility is also reflected.
These constructions require only commutative rings and their specified algebra
structure, with no topologies or finiteness conditions.

For any topologies on the four factor point spaces, if both factor maps are
open embeddings, `isOpenEmbedding_schemeCompatiblePairMap` proves that the map
of compatible-pair subspaces is an open embedding. The proof restricts the
product embedding and identifies its range as the inverse image of the product
map's open range under the target subtype inclusion. Monicity of the common
target map supplies the reflected compatibility needed for this range equality.
No topology on either common target point space is required.

This is an intrinsic chart construction and does not by itself assert the full
nonaffine fibre-product clause of Proposition 3.1.
