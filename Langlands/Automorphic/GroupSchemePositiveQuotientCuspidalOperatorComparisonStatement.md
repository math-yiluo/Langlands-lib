# Averaging the full cuspidal operator over the positive split centre

Let \(G\) be a connected reductive affine group scheme, locally of finite
type over a number field \(F\). Take a finite-rank split torus \(T\) with a
central map to \(G\) such that restriction of rational characters is
injective with finite-index image. Write \(A^+\) for the intrinsic positive
subgroup of \(T(\mathbb A_F)\), \(a n\) for multiplication by its image in
\(G(\mathbb A_F)\), and \(N = G(\mathbb A_F)^1\) for the norm-one group.
The statement uses the Library's parabolic structure and right invariance
of its Haar measure on \(N\), as in the original full cuspidal action.

`normOneFullAEL2CuspidalIntegratedAction` restricts the full adelic right
action to \(N\) and integrates the weighted orbit of each vector. The
operator acts on the existing space `fullAEL2CuspidalSubmodule` of
almost-everywhere cuspidal \(L^2\) classes on the positive rational quotient,
with the same quotient measure as `fullAEL2CuspidalIntegratedAction`.

`GroupSchemePositiveQuotientCuspidalOperatorComparisonStatement` takes a
complex weight \(f\) integrable for the existing ambient Haar measure.
Its positive-factor average

\[
  f^1(n) = \int_{A^+} f(a n)\, da
\]

is integrable for the existing Haar measure on \(N\). The measure \(da\) is
`normalizedPositiveHaarMeasure`, so that multiplication carries its
product with norm-one Haar to ambient Haar exactly. The bounded operator
of \(f^1\) for the restricted action equals the bounded operator of \(f\)
for the full adelic action. In particular any lift with this prescribed
average gives the same operator on the original cuspidal Hilbert space.

The identity is derived from the quotient comparison in Getz–Hahn
(2024), §2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF
pp. 85–86), and the integrated action and its cuspidal restriction
in (9.2) and (9.4), printed pp. 239–241 (PDF pp. 251–253).
Right translation descends through the positive quotient and hence
depends only on \(n\) in the product coordinates. Integrating that
orbit using the product Haar law gives the operator identity by Fubini.
The comparison uses integrable weights and applies in particular to
compactly supported smooth weights.

Source `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
