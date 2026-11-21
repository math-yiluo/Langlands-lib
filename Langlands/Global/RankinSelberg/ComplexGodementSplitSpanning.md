# Polynomial Gaussian tests split into compact-finite column products

`complexGodementSplitSpanning` expands each rectangular Gaussian polynomial as a finite sum over the monomials of its polynomial factor. The map from polynomials to Schwartz functions is complex linear, so the usual monomial expansion gives equality of actual Schwartz tests.

Each Gaussian monomial is a column product by `gaussianMonomial_eq_columnProduct`. For the square factor, express each real entry coordinate as half the sum of the entry and its conjugate. Express each imaginary coordinate using their difference. Polynomial substitution then identifies the real-coordinate Gaussian with the Gaussian in entries and conjugates at scale one. The established finite left unitary orbit bound for that class applies to the square factor.

These are the split tests and compact finiteness needed for the adjacent-rank unfolding. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.3](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
