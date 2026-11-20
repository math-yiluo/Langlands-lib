# Descent of split torus homomorphisms from torsion restrictions

For a split torus with character lattice \(\Lambda=\mathbb Z^L\), where
\(L\) is finite, `splitTorsionRestriction` is the homomorphism from the
diagonalizable group of \(\Lambda/n\Lambda\) to the one of \(\Lambda\) induced
by the lattice quotient. The comparison in `DiagonalizableTorsionCoordinates`
identifies this map with the actual torsion inclusion in diagonalizable
coordinates. `baseChangeMap_project` identifies the projection of a pulled-back
homomorphism with precomposition by scalar extension on the group algebra.

Let \(R\to K\) be injective and let \(G\) be an affine group scheme over
\(R\). A homomorphism from the split torus to \(G\) after base change to \(K\)
descends uniquely to \(R\) if its restrictions to the indicated torsion
subgroups descend as homomorphisms for an unbounded set of orders \(n\).
The proof of `existsUnique_baseChange_hom_of_torsion_lifts` obtains the
underlying map by affine coefficient descent. Schematic dominance checks
compatibility with the structure maps. The projection comparisons identify its
pullback with the given map over \(K\).

The group law reflection used in that last step also works for a flat source,
a separated target, and a quasi-compact schematically dominant base change
of arbitrary schemes. Flatness makes the base change schematically dominant
on the source, its relative square, and the base itself. Consequently the
unit and multiplication diagrams can be checked after pullback. The resulting
monoid morphism gives the group homomorphism, and schematic dominance on the
source gives uniqueness. The module derives these comparisons from the
Library's actual group pullbacks, torsion coordinates, affine coefficient
descent, and schematic homomorphism equality.
