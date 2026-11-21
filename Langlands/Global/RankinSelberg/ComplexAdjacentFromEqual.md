# The adjacent-rank step from the normalized equal-rank equation

`complexAdjacentFromEqual` proves the entire-normalized equation on the exact Whittaker models for adjacent ranks, assuming the lower equal-rank equation in its entire-normalized form with absolute convergence. `complexUnequalNormalizedRankTwoRankOne` applies it to the unconditional Tate base and gives the normalized equation for \(\mathrm{GL}_2(\mathbb C)\times\mathrm{GL}_1(\mathbb C)\).

In the lower equal-rank equation, take the Fourier transform of the original column as the row test and use the opposite additive parameter. Fourier inversion identifies its dual test with the original column, so the two equal-rank convergence clauses and the normalization give `HasAdjacentLowerEqualInputs`. Multiplicity one expresses both exact Whittaker vectors as canonical Jacquet values for their respective inducing lists. The larger vector uses the canonical parameter opposite to its Whittaker character. Substituting those values into `complexAdjacentCanonical` gives the exact pair factors and the sign for all inducing exponents.

The retained input concerns only the two representations at the smaller rank. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
