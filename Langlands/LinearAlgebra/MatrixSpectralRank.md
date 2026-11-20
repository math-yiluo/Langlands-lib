# Spectral rank labels for complex matrices

Matrix rank is lower semicontinuous over a complete nontrivially normed field. The map from a matrix to its continuous linear operator on column vectors is continuous, since application to each fixed vector is continuous and the domain is finite-dimensional. The rank superlevel sets are then pullbacks of the open rank superlevel sets for continuous linear maps.

For a complex \(n\times n\) matrix \(A\), a root \(z\) of its characteristic polynomial, and \(0\leq k\leq n\), the shifted power rank is \(\operatorname{rank}((A-zI)^k)\). It is lower semicontinuous jointly in \(A\) and \(z\). There are finitely many pairs of roots and powers at a fixed matrix. By combining the neighborhoods for those pairs with local matching of distinct roots, the proof finds arbitrarily close matches that preserve multiplicities and give a lower bound for every matched rank when the distinct root count stays fixed.

The label is the pair consisting of the number of distinct roots and the sum of these ranks, ordered lexicographically. Its first coordinate is at most \(n\), and its second is at most \(n^2(n+1)\). Both coordinates are preserved by conjugating by an invertible matrix and by transposition. The label is lower semicontinuous, so its strict superlevel sets are open. At fixed label, the sum of all matched ranks is unchanged. Each individual rank was bounded from below by the corresponding base rank, so equality of the sums forces equality term by term.

The label and these lemmas are internal constructions for an invariant filtration of matrix space. The fixed-label comparison supplies the local matching data for the generalized eigenspace ranks.
