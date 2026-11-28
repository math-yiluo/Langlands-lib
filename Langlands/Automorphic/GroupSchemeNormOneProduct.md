# Infinite and finite coordinates on the norm-one adelic group

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86),
use the positive central subgroup of the infinite group to identify the
positive quotient with the norm-one group over a number field. The
factorization following (9.2), printed p. 240 (PDF p. 252), uses the
archimedean quotient and the full finite adelic group as the two variables.

The module constructs these coordinates on the Library's actual norm-one
group. It takes an affine group scheme over a number field and a central
map from a split torus with a finite splitting. Restriction of rational
characters to this torus is assumed injective with finite-index image, as
in `normOneProjection`. The split torus's positive image lies in the
infinite factor, so `finite_normOneProjection` shows that removing the
positive coordinate preserves the finite point. For a pure infinite point
the projected point is still pure infinite. `infiniteNormOneProjection`
views it in `infiniteNormOneSubgroup`, with the same norm-one inclusion.

`normOneProduct` is a continuous multiplicative equivalence from
`infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G` to
`normOneSubgroup F G`. It pairs the two inputs and applies `normOneProjection`.
The inverse takes the infinite projection followed by
`infiniteNormOneProjection`, and the finite projection. The infinite
projection to the norm-one subgroup kills the infinite part of each
positive point, which gives the first inverse identity. For the second
identity, multiply the included pure infinite and pure finite parts and
use that `normOneProjection` fixes the original norm-one point.

The equivalence restricts on the infinite factor to `infiniteNormOneInclusion`.
On the finite factor it sends a finite point to the norm-one projection
of its pure finite inclusion. These formulas give the coordinates used in
the compactly supported test-function factorization.
