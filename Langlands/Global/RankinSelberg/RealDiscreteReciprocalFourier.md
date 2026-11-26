# Fourier estimates for real discrete-series angular modes

`realDiscreteAngularFourierBound` proves that the rank-two cell profiles
\[
  H_{k,j}(x)=(1+x^2)^{-(k+1)/2}\exp(ij\arctan x),
  \qquad k\geq 1,\quad j=\pm(k+1+2m),\quad m\geq0,
\]
are integrable. For each \(0\leq\eta\leq k\) their Fourier transforms satisfy \(|\widehat H_{k,j}(y)|\leq C|y|^\eta\) for all real \(y\). The Fourier phase is the Library's real phase \(e^{-2\pi ixy}\).

The arctangent identities express the positive angular mode as
\((1+ix)^m(1-ix)^{-(k+1+m)}\). The negative angular mode reflects the real variable, and reflection preserves the bound. The identity \(1+ix=2-(1-ix)\) gives a recursion in \(m\). At \(m=0\), `realLowestWeightFourier` identifies the transform on the positive half-line with a multiple of \(y^k e^{-2\pi y}\). It vanishes for negative \(y\). For \(0<y\leq1\), \(y^k\leq y^\eta\). For \(y>1\), the exponential series bounds \(y^k e^{-2\pi y}\) by a constant, and \(1\leq y^\eta\). Integrability and the bound then pass through the recursion by linearity and the triangle inequality.

This Fourier estimate is an internal step toward the real rank-two discrete-block estimate. The scalar tempered Whittaker estimate is discussed in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Proposition 3.4, author-posted p. 21. [Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
