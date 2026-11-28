# Finite vectors in finite orthogonal sums of canonical cuspidal representations

Work over a number field \(F\) with an affine, locally finite type,
connected reductive group \(G\). The statement uses the canonical quotient
\([G]=A_G G(F)\backslash G(\mathbb A_F)\) and `canonicalMeasure`. Its parameters
include the parabolic radical interface, a maximal compact subgroup \(K\)
of \(G(\mathbb A_F)\), a positive-size closed matrix realization, and the
smoothness and differential commutator hypotheses of the classical
automorphic space.

Let \(V_i\) be a finite orthogonal family of closed irreducible
subrepresentations of the actual right action on \(L^2([G])\), each contained
in `canonicalFullAEL2CuspidalSubmodule`. On the algebraic sum of these
subspaces, `GroupSchemeCanonicalCuspidalFiniteVectorComparisonStatement`
identifies membership in the square-integrable classical cuspidal image
with `IsCanonicalL2FiniteVector`. This means the orbit under the
archimedean factor \(K_\infty\) spans a finite-dimensional space and one
open subgroup of \(G(\mathbb A_{F,f})\) fixes the vector. The classical
image uses `IsAutomorphicFunctionOn` and requires pointwise vanishing
of the mass-one proper parabolic periods.

The comparison adapts Getz–Hahn's argument for Theorem 9.7.3, equations
(9.40) and (9.42), to the smoothness and finite-level convention of
Borel–Jacquet §§4.1–4.3. In this convention the representatives are
continuous, smooth on each archimedean slice, and fixed by one open
finite adelic subgroup. Getz–Hahn's Definitions 6.3.3 and 6.5.1 use the
algebraic tensor product in (6.1), which additionally puts every
archimedean slice in a single finite-dimensional space of functions.
The Library's `irreducibleSubrepresentationFiniteVectorAutomorphy`
supplies the representatives in the slice-wise convention.

The argument for (9.40) uses the finite sum of irreducibles from
Corollary 9.1.3 and recovers pointwise cuspidality using Lemmas 9.7.2 and
9.2.3. For the square-integrable classical image, the finite-sum
argument works for any supplied finite orthogonal family. Its summands
may have different unitary types.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024).
  Theorem 9.7.3, (9.40), (9.42) and the proof of (9.40), printed
  pp. 265–266 (PDF pp. 277–278). Equation (6.1) and Definitions 6.3.3
  and 6.5.1 are on printed pp. 158, 163 and 167 (PDF pp. 172, 177 and
  181). The literature identifier is `getz-hahn-2024-automorphic-representations`
  and the PDF SHA-256 is
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- Borel–Jacquet, *Automorphic Forms and Automorphic Representations*
  (1979), §§4.1–4.3, printed pp. 194–195 (PDF pp. 189–190).
  The literature identifier is `borel-jacquet-1979-automorphic` and
  the PDF SHA-256 is
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
