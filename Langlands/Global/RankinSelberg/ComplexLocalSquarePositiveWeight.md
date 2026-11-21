# Polynomial matrix norm weights in the equal-rank unfolding

This internal estimate supplies the matrix part of the convergence argument in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2, printed pp. 55–56. A Schwartz matrix test times a nonnegative integer power of `max 1 ‖g‖` is integrable with the specified determinant weight for any Haar normalization. Here the norm uses the matrix itself. The threshold on the determinant exponent is the matrix size for every such power.

The operator norm is bounded by a constant times one plus the sum of the squared entry norms. This last function and its powers have temperate growth, so multiplying the test by the corresponding power yields a Schwartz function. The published square matrix convergence theorem with height exponent zero then bounds the desired integral.

## Schwartz control of the integral

The integral of the absolute weighted test is also controlled by a continuous function of that test which vanishes at zero. The determinant density replaces the exponent \(p\) by \(p-n\) on the invertible matrix locus. A nonnegative polynomial majorizes this determinant power together with the matrix norm weight. Multiplication by that polynomial gives a continuous map on Schwartz space. The \(L^1\) norm of its output bounds the weighted integral.
