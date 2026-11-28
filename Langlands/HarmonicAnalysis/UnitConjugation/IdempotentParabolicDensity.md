# Locally integrable densities under idempotent parabolic conjugation

Let \(A\) be a finite-dimensional ultrametric normed algebra over a proper
nontrivially normed field. For an idempotent \(e\) let \(M\) be its
centralizer and \(U=eA(1-e)\) its upper corner. Take a compact open
set \(C\) of units in \(A\) and additive Haar measures
\(\mu_A,\mu_M,\mu_U\). Write \(\Phi(g,Y,Z)=g(Y+Z)g^{-1}\) on the chart.

`idempotentParabolicDensity` shows that if \(\theta\) is locally
integrable on \(M\), then the pushforward of the weight
\((g,Y,Z)\mapsto\theta(Y)\) against
\((\mu_A|_C)\otimes(\mu_M\otimes\mu_U)\) is represented on
Schwartz–Bruhat tests by a locally integrable density for any ambient
additive Haar measure \(\nu\). For the density \(r\), the identity is

\[
  \int_A r(X) f(X)\,d\nu(X)
  = \int_{C\times M\times U}\theta(Y) f\bigl(\Phi(g,Y,Z)\bigr)
      \,d\mu_A(g)\,d\mu_M(Y)\,d\mu_U(Z).
\]

## Proof

The unweighted Haar pushforward is absolutely continuous by
`idempotentParabolicAbsoluteContinuity`. To apply
`locallyIntegrablePushforward`, let \(K\subseteq A\) be a compact target
set. If \(g\in C\) and \(\Phi(g,Y,Z)\in K\), then \(Y+Z\) belongs to the
image of \(C\times K\) under \((g,X)\mapsto g^{-1}Xg\).
This image is compact, since inversion on the unit chart is continuous.
The diagonal and upper projections give compact sets of possible
values for \(Y\) and \(Z\). The Levi weight is integrable on the first
set by local integrability. The other two factors have finite mass
by compactness, so the product measure integrates the weight over the
preimage of \(K\) in the chart. `locallyIntegrablePushforward` now
supplies the density and the test identity.

## Source

This gives the local summability of the weighted conjugation integral
in a direct approach to parabolic descent for the idempotent Levi.
The test integral is the additive-coordinate form of the one in
Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups*, University Lecture Series 16, 1999, §1.4, pp. 9–10,
Lemma 1.13.
