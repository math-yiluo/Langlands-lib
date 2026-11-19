# Absolute convergence of the complex unequal-rank kernels

`complexLocalUnequalConvergence` proves that both kernels of
`ComplexLocalUnequalFunctionalEquationStatement` are integrable on a
single right half-plane for every pair of model vectors and every
compatible smaller-rank quotient measure. The proof takes the maximum of
the ordinary and dual bounds on the real part.

For the dual kernel, each quotient point is represented by the product of
a positive diagonal and a unitary matrix. The proof moves that unitary
factor out of the rectangular point and past the rectangular variable by
right multiplication of the variable by its inverse. The sum of squared
moduli of the rectangular entries is invariant under this multiplication.
The factored unitary and the unfolding Weyl element leave the Iwasawa
logarithms unchanged.

The rectangular bounds control the sum of the absolute Iwasawa logarithms
at the larger point and bound the sum of the positive diagonal logarithms
and the logarithmic rectangular size by the positive simple-root sum.
The dual Whittaker bounds have fixed growth exponents and arbitrarily
high decay order along the positive simple roots. The shifted
determinant weight has exponent coefficient \(2\operatorname{Re}(s)-(r-t)\)
against the sum of the diagonal logarithms. When this coefficient is
sufficiently large, the identity relating that sum to the sums of
positive parts and absolute values yields an integrable product bound
after choosing the simple-root decay order for the given \(s\).

The diagonal factor cancels the exponential density of the exact
quotient marginal and leaves the exponential of the negative sum of
absolute diagonal logarithms. The rectangular factor is bounded by a
product of \((1+|z|^2)^{-3}\), one factor for each complex entry. Each
factor is integrable for the self-dual additive Haar measure. The product
measure argument covers the shape with zero rectangular rows. Continuity
of the exact quotient kernel supplies measurability.

The pointwise majorization follows Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §5.2, pp. 33–35. The ordinary input implements §5.1,
p. 32.
