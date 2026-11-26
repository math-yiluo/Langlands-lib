# Strip growth of the complex GL₂ × GL₁ recursive ordinary tests

`complexAdjacentRankOneStripGrowth` gives an entire normalization of exponential strip growth for the actual ordinary complex \(\mathrm{GL}_2\times\mathrm{GL}_1\) integral on the split recursive tests. It assumes the explicit right-hand formula for the larger Whittaker function on the padded subgroup. The two smaller Whittaker vectors are in the character models for the opposite additive characters. The original three character blocks determine the indicated ordinary pair L-factor.

The published adjacent unfolding and absolute convergence identify the ordinary integral with a double integral. Since the smaller group is \(\mathrm{GL}_1\), translating its character coefficient multiplies it by the character of the translating determinant. The double integrand thus separates exactly into an ordinary rank-one kernel and a square zeta kernel twisted by the removed character. Their entire normalizations and exponential strip bounds are available separately. The two reciprocal denominators multiply to the full denominator, and the product of the normalized functions satisfies the required ordinary equality on a right half-plane.

The split recursive formula and unfolding use Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.3, equation (8.3), author-version pp. 58–60. The square integral and its normalization are in §4.7, equations (4.3)–(4.4) and Proposition 4.4, pp. 30–31. Here the smaller group has rank one, where a character gives the factorization directly. The statement retains the split recursive restriction formula as a hypothesis.

`pairFactor_two_one` splits the two-by-one pair factor into the product of its character factors.
