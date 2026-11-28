# Smooth slices on the quotient by the positive split centre

`GroupSchemePositiveQuotientSmoothnessStatement` concerns the actual
adelic points of an affine group scheme over a number field \(F\).
It takes the smooth relative dimension of the group, an embedded
`NormOneLieAtlas` on \(G(F_\infty)^1\), and a map from a finite-rank
split torus \(T\) into the centre of \(G\). Restriction of rational
characters to \(T\) is injective with finite-index image.

Write \(p\) for `normOneProjection`, which removes the intrinsic
positive image of \(T\) from an adelic point. The proposition gives
a smooth map \(p_\infty:G(F_\infty)\to G(F_\infty)^1\)
whose inclusion in \(G(\mathbb A_F)^1\) is \(p\) on points with
finite component \(1\). For every function \(f:G(\mathbb A_F)^1\to
\mathbb C\), it compares two conditions:

- For every finite point \(b\), the function \(a\mapsto f(p(a,b))\)
  is plot-smooth on the full archimedean group.
- For every norm-one point \(x\), the function
  \(a\mapsto f(x\,\operatorname{ofInfinite}(a))\) is smooth on the
  embedded archimedean norm-one group.

The proposition asserts their equivalence before rational quotienting.
It addresses the archimedean part of the smooth test condition.

## Source

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§2.6, equations (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
(PDF pp. 85–86), give the norm-one group, the archimedean positive split
centre and their product description. In §9.1, equation (9.2) and the
paragraph on printed p. 240 (PDF pp. 251–252) use tests on the quotient
by that centre with an archimedean smooth factor. The proposition
derives a comparison of the two smoothness conditions from the
product description using the actual adelic and Lie-group carriers.
The finite-level and compact-support conditions on the tests are
separate.

Literature ID `getz-hahn-2024-automorphic-representations`.
Retained PDF SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
