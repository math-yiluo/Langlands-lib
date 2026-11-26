# Polynomial traces of standard Gaussian equal-rank recursion tests

The product of a standard rectangular polynomial Gaussian and a standard polynomial Gaussian on the last row is a standard square polynomial Gaussian. The entries in the polynomial multipliers are renamed into their respective matrix positions. The squared norm of the matrix is the sum of the squared norms of its two blocks.

Assume `ComplexAdjacentPolynomialAtRank r (-a)`, which gives polynomial ordinary normalizations with the larger Whittaker factor at scale \(-a\) and the smaller factor at scale \(a\). Fix the compatible measures, the recursion data and the two polynomial Gaussian tests. The ordinary equal-rank unfolding identifies a nonzero scalar multiple of the ordinary integral with the double integral of the square product. The square polynomial family theorem and the identity of the two parts of the \(L\)-factor give a family of polynomials \(P_z\) whose values agree with the ordinary integral times the reciprocal equal-rank pair \(L\)-factor when \(\operatorname{Re}z>\tau\) and \(\operatorname{Re}s>\sigma\). The bounds are common to the family. Division by the nonzero Haar constant gives the polynomial for the ordinary integral.

This implements the ordinary chamber step of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2 and Proposition 8.1, author-posted pp. 54–58 and 60–61.
