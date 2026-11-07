# Separatedness from finite-set affine neighborhoods

Author: Worker 1203.

This internal support unit derives separatedness of an actual scheme from the
published `HasFiniteAffineNeighborhoods` predicate, which requires an affine
open neighborhood of every finite set of underlying points. No compactness,
closed-point, noetherian or finite-type hypothesis is imposed.

`FiniteAffineNeighborhoodsSeparatedStatement` asserts absolute separatedness
in arbitrary universe `u`. The direct lemma
`isSeparated_of_hasFiniteAffineNeighborhoods` gives separatedness of every
morphism with such a source, and `finiteAffineNeighborhoodsSeparated` proves
the named statement. The final lemma records quasi-separatedness of the
underlying topological space.

The proof chooses an affine open cover of the target and the cover by all
affine opens of each inverse image. The AF property passes to those inverse
images through their open immersions. For a point of the relative product,
the two projections lift over one common target chart. Their lifts lie in
one affine open of that inverse image, so the point lies in the square of
this affine open. Thus the diagonal squares cover the whole relative product.
Mathlib proves that the diagonal restricted to the union of such squares
is a closed immersion. Since this union is the whole product, the original
diagonal is a closed immersion. Applying the result to the terminal map gives
absolute separatedness, which implies quasi-separatedness by Mathlib.

The provenance is internal: the implemented proof uses finite-set affine
neighborhoods, the open-immersion inheritance theorem in
`FiniteAffineNeighborhoodsOpenShrinking`, and Mathlib's pullback point and
diagonal-cover APIs. It neither proves AF descent across a finite surjection
nor constructs a representation of an algebraic space.
