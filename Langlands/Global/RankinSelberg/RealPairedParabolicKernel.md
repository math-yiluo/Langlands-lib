# Doubly padded kernels of real parabolic lifts

`RealPairedParabolicKernelStatement` considers a pure smooth pair whose first coefficient has the leading-block restriction of a parabolic lift. At a cut strictly below both ambient ranks, its paired kernel at the terminal determinant exponent shifted by the comparison rank difference agrees with the lower ordinary unequal-rank kernel in the reversed order, multiplied by the lifted last-row profile.

The action on a pure smooth tensor factors into the two coordinate actions. Applying the paired Whittaker form therefore gives the product of the two coefficients at their respective embeddings. The terminal half-sum of rank gaps, plus the difference between the terminal and lower comparison ranks, is the half-sum of the two gaps at the lower rank. The half-determinant power of the parabolic lift cancels the gap of the first factor and leaves the ordinary determinant exponent of the reversed pair.

This is the kernel comparison when the leading Levi block has smaller rank than the second group, as used in [Jacquet, *Archimedean Rankin–Selberg Integrals*, Proposition 14.3 and Lemma 14.1, p. 105](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=105).

`pairedParabolicKernel_of_leading` allows the leading restriction in either slot. The product of coefficients and the sum of the determinant gaps are unchanged by the order of the two slots. The lower ordinary kernel puts the group of the uncut slot first.
