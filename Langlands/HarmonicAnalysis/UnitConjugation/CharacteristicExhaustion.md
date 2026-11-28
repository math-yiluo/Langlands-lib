# Invariant clopen exhaustion by characteristic size

Let `F` be a complete nontrivially normed ultrametric field and `A` a finite-dimensional normed `F`-algebra with a proper ultrametric norm metric. The sublevel `characteristicSublevel F n` consists of elements with characteristic size at most `n + 1`. Continuity gives closedness. Local constancy gives openness at points of positive size, and continuity gives openness at points of size zero. The sublevels are conjugation invariant and eventually contain each compact set.

Assume the unit sublevel is contained in the conjugation saturation of a compact set. For each `n`, multiply by a nonzero scalar of norm at most `1 / (n + 1)`. Homogeneity puts the scaled sublevel into the unit sublevel, so the original sublevel is contained in the conjugation saturation of the inversely scaled compact set.

`CharacteristicExhaustionStatement` assumes this saturation hypothesis, `1 < ‖d‖` and `0 < δ`. For each compact open additive subgroup `L` it gives a bound `b > 0`. For each `t ≥ b`, consider the conjugation-invariant distributions vanishing on indicators of `x + L` with `‖x‖ > t` and `x` outside `characteristicCone F δ`. If their image under restriction to `L`-invariant tests is finite dimensional, each of these distributions agrees on those tests with a conjugation-invariant distribution supported in the closure of the saturation of a compact set. The proof uses large-coset constancy to preserve vanishing under multiplication by each cutoff. Eventual agreement on individual tests and finite dimensionality give one cutoff with agreement on all `L`-invariant tests.

This implements the truncation in the extension of Howe's theorem. [Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, §11.2, Lemma 11.7 and Corollary 11.8, pp. 60–62](https://doi.org/10.1090/ulect/016)

`CharacteristicExhaustionCompleteUltrametricStatement` makes the completeness, ultrametric and properness hypotheses explicit.
