# Positive-rational subgroup measure of compact conjugates in adelic GL

`Langlands.Global.PositiveRealTorus.AdelicGLPositiveRationalConjugateGrowthStatement`
and its proof `adelicGLPositiveRationalConjugateGrowth` use the actual group-scheme
adelic points of `GL_n` over a number field `F`. Let `T → GL_n` be central, with
injective, finite-index character restriction and a finite split-torus
identification as in the Library's positive decomposition. Let `H` be the
positive-rational subgroup, with the canonical measure
`positiveRationalSubgroupHaarMeasure`.

Fix a compact subset `S` of the full adelic point group and a finite adelic
matrix point `b`. Let `x` be the point with matrix coordinates `(a, b)`. There
is a nonnegative `B` independent of the archimedean point `a` such that

\[
\mu_H(H\cap xSx^{-1}) \le B\,\bigl(\texttt{infiniteAdelicHilbertNorm}\ F\ n\ a\bigr)^{2d},
\qquad d=\dim_{\mathbb R}(\texttt{ArchimedeanMatrix}\ F\ n).
\]

Here the left side uses `Measure.real` on the subgroup subtype, with its
preimage under the inclusion into the ambient group. The proof bounds the
underlying extended measure by a finite product before taking real values.

## Implemented proof

Under `positiveRationalDecomposition` the subgroup measure is the product
of normalized positive Haar and counting measure on the principal norm-one
subgroup. The preimage of `H ∩ x S x⁻¹` lies in a rectangle:

- The positive coordinate belongs to the compact positive projection of `S`.
  The positive factor is a homomorphism to a commutative group, so it does not
  change under conjugation.
- For the norm-one coordinate, project `S` by `normOneProjection` and then
  transport it to the full adelic matrix group using `adelicHomeomorph`. This
  gives a compact matrix set independent of `x`. The positive image is central;
  commuting its inverse past `x` shows that the matrix projection of
  `x s x⁻¹` is the conjugate of the matrix projection of `s` by the *original*
  matrix element `(a, b)`. In particular the finite coordinate used for the
  count is the fixed `b`.

Identify each principal norm-one point with its unique rational matrix. The
second factor of the rectangle is the pullback to these points of the finite
set counted by `adelicGLCompactConjugateCounting` for that compact matrix set.
The product measure of the rectangle is at most the fixed positive Haar mass
of the first factor times the matrix-point count. The first mass is finite by
compactness and the Haar property. The counting estimate then gives the real
polynomial bound.

## Provenance and scope

This is a derived growth estimate from the Library's exact subgroup Haar
normalization and compact-conjugate rational point count. It supplies the
subgroup-measure factor in the bound for compact convolution on the positive
rational quotient. The context is the summand-to-realization direction of
Getz–Hahn, *An Introduction to Automorphic Representations*, Springer GTM 300
(2024), Theorem 9.7.3, pp. 265–267 (PDF pp. 277–279), by the Library's route
using that convolution estimate. This module does not prove the existence of
a continuous representative, smoothness, a bound uniform in the finite
component, or the realization theorem.
