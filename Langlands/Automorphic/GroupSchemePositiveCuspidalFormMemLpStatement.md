# Square integrability of descending classical cuspidal forms

Let \(G\) be an affine locally finite type connected reductive group
over a number field \(F\). Take the smooth relative-dimension witness,
archimedean differential commutator identity, maximal compact subgroup
of \(G(F_\infty)\), closed matrix embedding of positive size, and
parabolic-dynamic statement used by the classical cusp-form space.
Use the Library's finite-level, plot-smooth realization with compact
and enveloping-centre finiteness and moderate growth.

Let \(i:T\to G\) be central with a specified finite-rank splitting
of \(T\), and assume its rational character restriction is injective
with finite-index image. In the split coordinates, the positive
real torus is embedded diagonally at the infinite places with
finite coordinate one. Its image \(A_i\) gives
\(Q=A_iG(F)\backslash G(\mathbb A_F)\). For a split component,
`imageSubgroup_eq_canonicalSubgroup` identifies \(A_i\) with the
positive split centre \(A_G\) in (2.20). The measure on \(Q\) is
the original norm-one quotient Haar measure pushed forward through
the inclusion-induced homeomorphism in (2.22).

`GroupSchemePositiveCuspidalFormMemLpStatement` applies to a
continuous function on \(Q\) whose pullback belongs to the original
classical cuspidal space. Its proper radical constant terms vanish
at every point for the probability Haar measures on the actual
quotients \(N(F)\backslash N(\mathbb A_F)\).
The conclusion gives a uniform bound on \(Q\) and membership in
`MemLp` with exponent \(2\) for the given quotient measure.

Getz–Hahn use the boundedness consequence of rapid decay and the
finite volume of \([G]\) in the first step of the proof of Theorem
9.7.3. The Library's reduced-representative decay gives this
consequence at height power zero. Rational invariance and the
norm-one quotient comparison give the bound on \(Q\). This is the
square-integrability input for the existing classical cusp-form
realization in `GroupSchemeCuspidalFormL2`.

## Sources

- `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Section 2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
  (PDF pp. 85–86). Theorem 9.7.1 and the first paragraph of the proof
  of Theorem 9.7.3, printed pp. 264–265 (PDF pp. 276–277).
- `moeglin-waldspurger-1995-spectral-decomposition`,
  registered folder SHA-256 `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`.
  Chapter file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`.
  I.2.12 and its corollary, printed pp. 34–35 (chapter PDF pp. 17–18).
  I.2.18, printed p. 39 (chapter PDF p. 22), gives the cuspidal
  specialization.
