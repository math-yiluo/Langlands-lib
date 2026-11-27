# Decay of a difference with vanishing smooth tests

The truncation sector is stable under positive scaling and contains a unit
vector. Above a radius \(R \geq 1\), an exponential increment bound with
constants uniform on each compact subset gives locally uniform convergence on
the open spectral domain \(U\) in a finite-dimensional real normed space.
The functions \(f(t,\cdot)\) are assumed continuous on \(U\) for all
sufficiently large \(t\) in the sector, so the limit is continuous on \(U\).

The spectral measure is Borel, finite on compact sets and positive on
nonempty open sets. Every real-valued smooth test with compact topological
support in \(U\) is assumed to have limiting integral zero. The limit then
vanishes on \(U\). On any subset of \(U\) where the increment estimate holds
with constants \(B\geq 0\) and \(\epsilon>0\), the bound at every point of that
subset and every sector parameter \(t\) with \(\|t\|\geq R\) is
\[
  \|f(t,x)\|\leq \frac{B e^{-\epsilon\|t\|}}{1-e^{-\epsilon}} .
\]

The sector filter is nontrivial by restriction to a positive ray. The
pointwise limits obtained from the increment estimate agree with the uniform
limits on compact subsets. Multiplying by a smooth compact test gives
measurable products and lets dominated convergence pass to the limit of the
integrals. The limit function thus vanishes almost everywhere on the domain.
Continuity and positivity of the measure on nonempty open sets give
pointwise vanishing.

This is the analytic argument in (7.27) and Lemma 7.7 of P. Delorme,
*On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, pp. 31–32. The registered PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
The difference in that application is the characteristic pairing minus the
regularized pairing, on the open set where the two tested limits vanish.
