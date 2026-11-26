# Exponential limits from increment estimates on a sector

`ExponentialSectorLimitStatement` concerns a map \(f\) from a real normed space
to a complete metric space. The sector \(C\) contains a unit vector and is
closed under all positive real scalings. For \(x,y\in C\) with
\(R\leq\|x\|\) and \(\|y\|\leq\|x\|\), suppose
\[
d(f(x),f(x+y))\leq B e^{-\epsilon\|x\|},
\qquad R\geq1,\quad B\geq0,\quad\epsilon>0 .
\]
There is a common limit \(L\) along the filter defined by membership in
\(C\) and \(\|x\|\to+\infty\). For every \(x\in C\) with \(R\leq\|x\|\),
\[
d(f(x),L)\leq \frac{B e^{-\epsilon\|x\|}}{1-e^{-\epsilon}} .
\]

`exponentialSectorLimit` uses steps of length one along each unit ray.
Starting at radius \(r\geq R\), the successive distances are bounded by
\(B e^{-\epsilon r} (e^{-\epsilon})^n\). Completeness gives a limit on the
reference ray starting at \(R\). To compare another ray at the same radius,
apply the increment bound twice at the sum of the two vectors. A starting
radius \(r\) on the other ray is compared with \(R\) by a shift of length
\(r-R\), which is at most the current radius once that radius is large
enough. These comparisons tend to zero, giving the same limit for every
ray and every start. Summing the geometric bound from the actual starting
point gives the displayed estimate. Its right hand side tends to zero
along the sector filter.

This is a quantitative form of the limit argument following Delorme's
Lemma 7.2 that gives (7.27). The sector of truncation parameters
\(d_{P_0}(T)\geq\delta\|T\|\) with strict dominance is closed under positive
scaling. If it contains a nonzero vector, it contains its normalization.
For a sufficiently large lower bound on \(\|T\|\), Lemma 7.2 with \(k_0=1\)
gives the stated increment bound, with \(B\) including the polynomial
factor in the fixed central translate. The summation factor depends only on
the exponential rate and so preserves any uniformity of that bound in the
spectral parameter.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, Lemma 7.2 p. 26 and the
argument at (7.27) p. 31. The published PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
