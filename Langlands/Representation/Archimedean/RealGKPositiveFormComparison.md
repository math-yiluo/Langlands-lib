# Invariant form comparison for real `(𝔤, K)`-modules

`RealGKPositiveFormComparisonStatement` assumes the real module condition
and the hypotheses of the Library's Schur lemma. The latter give
irreducibility, admissibility, compact finiteness and continuity of the
compact matrix coefficients. Given an infinitesimally invariant positive
Hermitian form \(b\), any sesquilinear form \(B\) with the same compact
invariance and real Lie algebra skewness is a complex scalar multiple of
\(b\).

The proof maps both forms to conjugate-linear maps from the module to
its finite contragredient. The map attached to \(b\) is an equivalence.
Composing its inverse with the map attached to \(B\) gives a linear
endomorphism. The two forms' invariance identities imply that this
endomorphism intertwines the compact action and the real Lie action.
The latter intertwining extends to the complexification by linearity.
The Library's `GKModuleDensity.exists_eq_scalar` gives the scalar.
Evaluating the two finite-dual maps recovers the claimed comparison of
forms.

`realStandardDensityHyp` checks the Schur hypotheses for an irreducible
real standard module. It uses admissibility of standard modules, their
finite orbit spans, and continuity of every coefficient on a
finite-dimensional orbit span.

This is an internal consequence of the Library's algebraic
contragredient and Schur lemma. It allows the sign of an induced
compact form to be compared with an existing positive form.
