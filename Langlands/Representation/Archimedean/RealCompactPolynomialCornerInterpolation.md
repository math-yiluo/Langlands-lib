# Interpolation of the compact braid corner expressions

The recursive middle expressions of `RealCompactPolynomialFullBraid` are
polynomials in their complex argument. The definitions here use polynomials
with coefficients in the same associative algebra. Evaluation is
multiplicative because the chosen complex argument maps into the centre.

At recursion index \(a\), both polynomials have degree at most \(a\) and
coefficient \(D_a(Z)\) in degree \(a\). The coefficient in degree two of each
new quadratic multiplier is \(Z^2+(a+1)^2\). The recurrence for \(D_a\) and
its commutation with \(Z\) yield the same top coefficient for either
multiplication order.

The difference therefore has degree below \(a\) when \(a>0\). Composing
coefficient evaluation with any complex linear functional gives a scalar
polynomial of degree below \(a\). If the difference vanishes at the first
\(a\) natural numbers, each scalar polynomial vanishes by the root bound.
Linear functionals separate points, so the difference is zero. At \(a=0\)
the two expressions both equal one.
