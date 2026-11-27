# Smooth-vector factorization for reductive adelic groups

Let \(G\) be a connected reductive group over a number field \(F\).
Use the actual decomposition of \(G(\mathbb A_F)\) into its infinite
and finite point groups and the Library's archimedean atlas. Let \(\pi\)
be a jointly continuous representation of \(G(\mathbb A_F)\) on a
complex Banach space. A vector \(v\) is assumed smooth for the
restricted archimedean action and fixed by some open subgroup \(L\)
of the finite adelic points.

`AdelicSmoothVectorFactorizationStatement` gives a finite expression
\[
v=\sum_i\int_{G(\mathbb A_F)} k_i(g)\,\pi(g)w_i\,dg.
\]
Each \(w_i\) is smooth for the restricted archimedean action. Each
\(k_i\) is a full-group test function. It is continuous with compact
support and smooth infinite slices, and has open finite levels for
left and right translation. The scalar kernels and the weighted
Banach-valued orbits are integrable for the original full adelic Haar
measure `Measure.haar`.

The archimedean step applies Dixmier–Malliavin to the closed linear
realization of the infinite factors. At the finite places, the
indicator of a compact open subgroup of \(L\), divided by its Haar
mass, fixes \(v\) by integration. The factor relating the product Haar
measure to \(dg\) is absorbed in the kernels. This gives the
factorization on the full group for the cuspidal application of
Getz–Hahn Corollary 9.6.5, where the book uses test functions on
\(A_G\backslash G(\mathbb A_F)\).

## Sources

- `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Theorem 4.2.8, printed p. 110 (PDF p. 125), and Corollary 9.6.5 and
  its proof, printed p. 264 (PDF p. 276).
- `dixmier-malliavin-1978-factorisations`, retained English translation,
  SHA-256 `b9ae377268ddfe90468dfcf21d08ee57df6a40496ba3c57276795a8ebbf5f07f`.
  Theorem 3.3 and its proof, PDF pp. 8–9.
