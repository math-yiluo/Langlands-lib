# Fixed-profile cuspidal finiteness on the canonical adelic quotient

`GroupSchemeCanonicalFixedProfileCuspidalFinitenessStatement` concerns an
affine, locally finite type, connected reductive group \(G\) over a number
field \(F\). It uses the canonical quotient
\([G]=A_GG(F)\backslash G(\mathbb A_F)\) and its Haar measure
`canonicalMeasure`. Fix a closed matrix embedding of positive size, the
archimedean differential calculus, and a maximal compact subgroup \(K\) of
\(G(\mathbb A_F)\). Write \(K_\infty\) for the inverse image of \(K\) in
\(G(F_\infty)\).

Fix a finite-codimension ideal \(J\) of the complex enveloping-algebra centre,
an open subgroup \(L\) of the finite adelic group, and a finite-dimensional
complex subspace \(E\) of functions on \(K_\infty\). The statement gives a
finite-dimensional complex submodule of \(L^2([G])\) with exact membership.
A class belongs to it precisely if it lies in the full almost-everywhere
cuspidal submodule and has a scalar automorphic representative \(\phi\) on
the adelic points. The representative is left invariant under \(A_G\),
right invariant under \(L\), annihilated by \(J\) on every infinite slice,
and has \(k\mapsto\phi(gk)\) in \(E\) for every adelic \(g\). Its values at
the chosen coset representatives agree with the class almost everywhere.

This is the transfer of fixed-type cuspidal finiteness used in the
number-field case of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 9.7.3. The argument after (9.43), printed
pp. 266–267 (PDF pp. 278–279), bounds the fixed-type cuspidal Hilbert
subspace by the finite-dimensional space of fixed-type cusp forms
using Theorem 6.3.4. Here \(E\) prescribes the entire compact profile
space, and `fixedProfileCuspidalFiniteness` applies to the corresponding
submodule of the original form carrier. Theorem 6.3.4, printed
pp. 164–165 (PDF pp. 178–179), gives the admissibility statement for
fixed central ideal and compact types at a compact open finite level.
The Library's cuspidal finiteness theorem uses the given space of
profiles and an open finite level. The scalar representative
conditions agree with the output of `SquareIntegrableProjectionAutomorphyStatement`.
The statement concerns classes already supplied with such representatives.

The literature identifier is `getz-hahn-2024-automorphic-representations`.
The retained PDF has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
