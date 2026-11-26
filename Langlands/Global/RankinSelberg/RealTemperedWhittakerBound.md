# The tempered Whittaker bound on the exact real coefficient model

Let the real block exponents have zero real part. `RealTemperedWhittakerBoundAtRank r` asks that every element of the specified real Whittaker coefficient model for \(\mathrm{GL}_{r+1}(\mathbb R)\) satisfy

\[
  |W(a(y)k)|\le C_{W,\epsilon}\,\delta(a(y))^{1/2}
       \exp\!\bigl(\epsilon\textstyle\sum_i|y_i|\bigr)
       \qquad (\epsilon>0).
\]

Here \(a(y)=\operatorname{diag}(\exp y_i)\), \(k\) ranges over the orthogonal group, and \(\delta\) is the upper triangular modulus. The statement is the estimate with exponential loss needed in the positive-half-plane convergence argument. It is adapted from Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 3.4, p. 21 of the author-posted edition. Jacquet treats continuous Whittaker forms on a tempered smooth representation and obtains a polynomial in the logarithmic diagonal. That polynomial is bounded by a constant times the small exponential for each \(\epsilon>0\). The formal statement is for the exact real coefficient submodule and requires the estimate for all its elements.

`realTemperedWhittakerBoundAtRank_zero` proves this statement for \(\mathrm{GL}_1(\mathbb R)\). The rank-one model calculation expresses each coefficient as a constant times the character evaluated on the determinant. With an imaginary exponent the character has norm one, and the modulus is trivial. At any rank, `hasTemperedDerivativeBound_of_model` deduces the right-derivative bound from the coefficient estimate because the exact model is closed under each iterated right derivative.
