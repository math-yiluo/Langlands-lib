# Complex adjacent-rank strip growth for Gaussian-polynomial tests

`complexAdjacentGaussian_rightIntegrable` proves absolute convergence on a
right half-plane for the ordinary adjacent-rank integral of a continued
Godement value attached to a rectangular Gaussian-polynomial Schwartz test.
The inputs are the quotient measure and the two smaller Whittaker model vectors,
with their inducing lists of the prescribed lengths.

The polynomial Gaussian splits into finitely many column products. Absolute
integrability of the Godement integrals gives additivity in the test. For each
split test the unfolded double kernel is absolutely integrable on a right
half-plane. Undoing the quotient shear and integrating the group variable gives
the original ordinary kernel. The maximum of the finitely many lower bounds on
the real part gives a common half-plane for the sum.

`complexAdjacentGaussianStripGrowth` assumes that the smaller equal-rank
integrals of the fixed first vector admit entire normalizations of exponential
strip growth. Under that premise it gives a normalized adjacent integral of the
same growth, together with right-half-plane absolute convergence. The
split-test strip theorem supplies the individual normalized continuations. Their
sum agrees with the original integral on a common right half-plane and retains
the strip bound. Additive induction over intertwiner ranges gives the conclusion
for every second Whittaker model vector.

This implements the ordinary split-test part of §8.3, equation (8.3) and
the following compact expansion, author pp. 58–60, in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009). The Gaussian-polynomial
family uses the Library's Gaussian of coefficient one. The source
describes its standard Schwartz family on p. 10.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
