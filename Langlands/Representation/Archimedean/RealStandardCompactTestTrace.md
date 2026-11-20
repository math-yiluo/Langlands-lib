# Compact trace comparison for continuous tests

The compact column integral from the polynomial averaging trace makes
sense for every continuous function \(\varphi\) on \(O(n)\). Its column
is \(\varphi(\widehat{\kappa}(x)^{-1}y)\) on the real group, where
\(\widehat{\kappa}\) is the signed orthogonal part of the Library's
principal series extension. Apply the sign and rotation filters, evaluate
at \(\widehat{\kappa}(yg)\), multiply by the radial extension factor
at \(yg\), and integrate over \(y\). This defines `compactTestTrace`.
For a block list of total rank \(n\), a Haar measure on \(O(n)\) of
arbitrary normalization, and any \(g\in GL_n(\mathbb R)\), it equals
`averageTrace` on polynomial tests with that Haar measure.

The columns vary continuously in both variables. The finite sign
averages preserve joint continuity and the Fourier integrals preserve
it by integration over a fixed compact interval. The sign averages
have norm bound one on bounded columns, and each high-mode filter has
bound one plus its number of removed modes. Together with the bounded
radial factor over the compact integration domain, this gives
continuity in the uniform norm of the test. Stone–Weierstrass density
and polynomial trace invariance give `realStandardCompactTestTrace`.
Suppose both block lists have total rank \(n\) and their actual standard
modules are joined by a bijective compact and Lie intertwiner. Using the
same Haar measure on \(O(n)\) for both integrals, the theorem gives equality
for every continuous compact test and every \(g\in GL_n(\mathbb R)\).

The internal result allows compact tests supported near the identity
in evaluating the regular character values.
