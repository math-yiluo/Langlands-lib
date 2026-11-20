# Simple-root majorization for complex local Whittaker functions

`ComplexWhittakerSimpleRootMajorizationStatement` bounds each derivative word of
a vector of the complex local Whittaker model on matrices of the form \(b(y)k\).
Here `logTorus y` is \(b(y)=\operatorname{diag}(\exp y_j)\), and \(k\) is
unitary. For each vector there is an integer \(N\) such that every word and
decay order \(M\) admit a constant \(C\geq 0\) with the bound

\[
C\exp\left(N\sum_j|y_j|-M\sum_i\max(y_i-y_{i+1},0)\right).
\]

The proof uses the adjacent elementary matrix scaled by the inverse of the
additive character parameter \(a\). Conjugation by \(b(y)\) multiplies that
matrix by \(\alpha_i=\exp(y_i-y_{i+1})\). The unipotent differentiation formula
from `ComplexLocalWhittakerRegularity` gives the multiplier \(4\pi\mathrm{i}\,\alpha_i\)
at \(b(y)k\) for the right derivative in the direction conjugated by \(k^{-1}\).
The coordinates of this direction in a real matrix basis are bounded on the
unitary group by continuity and compactness.

For a finite list of roots, the proof bounds the derivative word multiplied
by the product of the clamped ratios \(\max(1,\alpha_i)\). An induction uses
\(\max(1,\alpha_i)\leq 1+\alpha_i\) and expands the extra derivative in the
fixed real basis. Uniform derivative growth gives one matrix-height exponent
for the base case with any word. Repeating every root \(M\) times converts
the product to an exponential of the sum of the positive root logarithms.
The matrix height of \(b(y)k\) and its clamp are bounded using the entry
bounds of the unitary matrix and its inverse, producing the factor in
\(\sum_j|y_j|\).

This is an internal estimate on the Library model, derived from the argument
in Jacquet 2009, §3.2, pp. 15–16, equations (3.11)–(3.12) and Proposition 3.1.
The constants are for each individual model vector and derivative word.
The bound is stated on the diagonal times the unitary group. Applying it to
the local integrals still requires the quotient measure and block estimates.

`ComplexLocalWhittakerGauge.height_logTorus_mul_le` gives the height bound on a logarithmic diagonal times a unitary matrix, independently of the Whittaker vector.
