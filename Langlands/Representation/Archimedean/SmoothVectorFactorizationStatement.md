# Factorization of smooth vectors for a closed linear Lie group

Let \(G\) be a real Lie group with a closed linear realization in the
unit group of a finite-dimensional real Banach algebra. The realization
identifies its manifold structure with the exponential charts on the
image. Let \(\mu\) be a left Haar measure on \(G\), and let \(\pi\) be a
jointly continuous representation on a complex Banach space \(E\) by
bounded linear maps.

`SmoothVectorFactorizationStatement` says that a vector \(v\) whose
orbit map \(g\mapsto\pi(g)v\) is real \(C^\infty\) has a finite
expression
\[
v=\sum_i\int_G k_i(g)\,\pi(g)w_i\,d\mu(g).
\]
Each \(w_i\) is smooth for the same action of \(G\). Each \(k_i\) is a
complex smooth function whose compact support lies in the prescribed
neighborhood of the identity. The proposition records integrability
of each Banach-valued orbit average for the given left Haar measure.

This is the complex Banach, closed linear Lie group case of
Dixmier–Malliavin, Theorem 3.3, which treats continuous representations
of Lie groups on Fréchet spaces. The identity uses the original
\(\pi(g)\) in the integrated action. The linear realization supplies
coordinates of the second kind for \(G\). No action of the ambient
unit group enters the hypotheses. The archimedean factorization is the
smooth-vector step used by Getz–Hahn in Corollary 9.6.5, where the
finite adelic level is handled by a compact open subgroup.

## Sources

- `dixmier-malliavin-1978-factorisations`, retained English translation,
  SHA-256 `b9ae377268ddfe90468dfcf21d08ee57df6a40496ba3c57276795a8ebbf5f07f`.
  Theorem 3.3 and its proof, PDF pp. 8–9. Lemma 2.5 and Remark 2.6 give
  the local one-variable identity. Theorem 3.1(1), PDF p. 6, supplies
  the Haar-coordinate step used in the proof.
- `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Theorem 4.2.8, printed p. 110 (PDF p. 125), and Corollary 9.6.5,
  printed p. 264 (PDF p. 276).
