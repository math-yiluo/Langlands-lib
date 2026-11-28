# Algebraic decomposition of classical cusp forms in the canonical Hilbert space

Fix a connected reductive group over a number field with the affine and finite-type
hypotheses, parabolic input, maximal adelic compact subgroup, positive-size closed
matrix embedding and differential calculus in the statement. Write \(S\) for
`canonicalFullAEL2CuspidalSubmodule`, formed with the canonical measure on
\([G] = A_G G(F) \backslash G(\mathbb A_F)\). Write \(C\) for the subspace of \(S\)
whose classes belong to `canonicalCuspidalFormL2Image`. This image represents
continuous, square-integrable classical cusp forms. Its compact finiteness uses the
archimedean factor of the given maximal compact subgroup, and its cusp condition
uses the mass-one measures of the unipotent radical quotients.

`GroupSchemeCanonicalCuspidalAlgebraicDecompositionStatement` takes an internal
Hilbert sum of \(S\) by complete subspaces \(P_i\) preserved by the canonical
adelic right action. Each orthogonal projection onto \(P_i\) carries \(C\) into
\(C\). Every vector in \(C\) is a finite sum of its projections. The intersections
with the \(P_i\), expressed as submodules of \(C\) by comap along the inclusion,
form an internal algebraic direct sum of \(C\).

The source is Getz–Hahn, *An Introduction to Automorphic Representations*
(`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`),
Theorem 9.7.3, (9.41) and the number-field argument following (9.43),
printed pp. 265–267 (PDF pp. 277–279). The book uses the cuspidal isotypic
Hilbert sum and applies Theorem 6.3.4 to each fixed finite adelic level,
cofinite central ideal and finite collection of compact types. The statement
isolates that algebraic step for a supplied invariant Hilbert sum and for the
classical \(L^2\) image. It applies in particular to the isotypic sum when
that sum is given.
