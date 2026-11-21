# Dilation of complex Godement tests and their strip estimate

`continuedValue_dilateMatrixTest` computes the effect of replacing the
rectangular test `Φ(X)` by `Φ(z X)` for a nonzero complex scalar `z`.
The change multiplies the continued value by the smaller Whittaker
central character at `z` and the determinant weight at the inverse
scalar matrix. The multiplier depends on the inducing data and the
added exponent.

The inner column kernel at `h` of the dilated test is the original
column kernel at `z h`. Changing the outer Haar variable by left
multiplication by the inverse scalar matrix gives the same integral
with the smaller Whittaker argument right translated by `z`. Its
central character law and the multiplicativity of the determinant
weights give the multiplier.

`ComplexAdjacentDilatedGaussianStripGrowthStatement` applies this
identity to a Gaussian-polynomial test. At the fixed inducing data the
multiplier is constant in the adjacent integral parameter. Absolute
convergence and the entire normalized strip bound thus transfer by
scalar multiplication.

The dilation is a derived identity for the continued form of
Jacquet's (7.6), §7.2, author pp. 47–50. It allows a change in the
Gaussian scale of the tests used in §8.3, pp. 58–60, with the source's
standard Schwartz convention on p. 10. [Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
