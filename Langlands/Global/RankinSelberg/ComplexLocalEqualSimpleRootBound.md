# From simple-root bounds to the complex equal-rank kernel bound

For \(x\in\mathbb R^{r+1}\), let
\(S(x)=\sum_{i<r}\max(x_i-x_{i+1},0)\). A simple-root bound in this
module has the form
\[
\left|W\bigl(\operatorname{diag}(e^{x_i})k\bigr)\right|
\le C_L e^{M\sum_i |x_i|-L S(x)}
\quad\text{for every }L\ge 0.
\]
The exponent \(M\) is fixed as \(L\) varies, while the constant \(C_L\)
may depend on \(L\). This is the logarithmic form of the estimate
used in Jacquet's Proposition 3.1, printed and PDF pp. 15–16 of
*Archimedean Rankin–Selberg integrals* (2009). The root gauge in
(3.3) bounds \(e^{2S(x)}\) from below, and on the diagonal the height
is a sum of squares of the diagonal entries and their inverses.

Each \(x_i\) is at most \(x_r+S(x)\) by telescoping the adjacent
differences. Hence \(P(x)\le (r+1)(\max(x_r,0)+S(x))\).
The last row at \(\operatorname{diag}(e^{x_i})k\) is \(e^{x_r}\)
times the last row of \(k\). The norm of the latter is positive
and has a positive minimum on the compact unitary group. A weighted
Schwartz seminorm thus supplies decay of any order in \(\max(x_r,0)\).
When \(x_r\le 0\), the zeroth seminorm gives a uniform bound.

For two coefficients with the simple-root bound, add their fixed growth
exponents to get \(M\). Use the root decay of the first coefficient
and the Schwartz last-row decay, both with exponent \((L+M)(r+1)\).
The telescoping inequality then gives the product bound
\(C_L e^{M Q(x)-L P(x)}\) required by
`ComplexLocalEqualTorusConvergence.lean`.
