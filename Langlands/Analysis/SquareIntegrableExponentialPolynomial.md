# Nondecaying exponents in a square-integrable exponential polynomial

`SquareIntegrableExponentialPolynomialStatement` concerns a finite sum
\(f(t)=\sum_j e^{tz_j}q_j(t)\), where the complex exponents \(z_j\) are
distinct and the coefficients \(q_j\) are complex polynomials. If \(f\) is
square integrable on the positive ray with Lebesgue measure, then each
\(q_j\) with \(\operatorname{Re}z_j\geq 0\) is zero.

The proof chooses a positive shift small enough that the numbers \(hz_j\) lie
in the injectivity strip for the complex exponential. The operator
\(f(t+h)-e^{hz_k}f(t)\) preserves square integrability on the ray because the
translated ray is a subinterval of the original ray. On the polynomial at
\(z_k\) it acts by a finite difference, which lowers its degree when it is
nonzero. On every other nonzero polynomial its leading coefficient is
multiplied by the nonzero difference of the two exponential multipliers.
Induction on the sum of the degrees plus one for the nonzero polynomials
isolates any chosen term of nonnegative real part. A nonzero polynomial is
bounded below in norm by a positive constant on a tail. The exponential has
modulus at least one there, so the isolated term cannot be square integrable.

This is a one-variable analytic ingredient for excluding boundary exponents
in square-integrable constant terms. Its premise is square integrability of
the scalar exponential polynomial with the exponential normalization already
made. The corresponding adelic constant-term slice and the full criterion on
several cone directions require additional arguments. The finite-difference
method is also used in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §6.4. For the use of strict
exponent inequalities, see E. Lapid, *On Arthur’s asymptotic inner product
formula of truncated Eisenstein series*, 2011, §6, Lemma 6, pp. 322–323.
