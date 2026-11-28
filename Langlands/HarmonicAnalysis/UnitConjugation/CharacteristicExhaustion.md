# Invariant clopen exhaustion by characteristic size

The sublevel `characteristicSublevel F n` consists of elements with characteristic size at most `n + 1`. Continuity gives closedness. Local constancy gives openness at points of positive size, and continuity gives openness at points of size zero. The sublevels are conjugation invariant and eventually contain each compact set.

Assume the unit sublevel is contained in the conjugation saturation of a compact set. For each `n`, multiply by a nonzero scalar of norm at most `1 / (n + 1)`. Homogeneity puts the scaled sublevel into the unit sublevel, so the original sublevel is contained in the conjugation saturation of the inversely scaled compact set.

`CharacteristicExhaustionStatement` applies these sublevels to the cutoff argument for a compact open lattice. Above a sufficiently large bound, membership in each sublevel is constant on cosets centered outside the characteristic cone. If the space of restrictions with this vanishing is finite dimensional, the restriction of an invariant distribution with this vanishing equals the restriction of a distribution supported in the closure of the conjugation saturation of a compact set. The proof uses the finite-dimensional cutoff argument with the verified sublevels.

This implements the truncation in the extension of Howe's theorem. [Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, §11.2, Lemma 11.7 and Corollary 11.8, pp. 60–62](https://doi.org/10.1090/ulect/016)
