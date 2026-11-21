# Real Haar integration over the full diagonal torus

`Langlands.GodementJacquet.RealTriangularHaarStatement` gives a Haar measure identity for `GL_n(ℝ)`. For any left Haar measure `μ` on the group, additive Haar measure `ν` on `ℝ`, and Haar measure `κ` on `O(n)`, there is a positive constant `c` such that `μ` is `c` times the pushforward of

\[
 \left(\prod_{i=1}^n \frac{dt_i}{|t_i|}\right)\,\left(\prod_{i<j}d\nu(x_{ij})\right)\,d\kappa(k)
\]

by `(t,x,k) ↦ diag(t) u(x) k`. Here every `t_i` ranges over **all** of `ℝˣ`, and `u(x)` is the upper unipotent matrix with entries `x_{ij}`. In Lean, `realDiagonalHaar` is the product of the Library's `RealRankZero.unitsHaar` measures. The scale absorbs the choice of Haar normalizations and the use of the full torus. The statement asserts a measure equality, not uniqueness of the coordinates on the group.

## Implemented proof

`realTriangularCoordinates` is a homeomorphism from diagonal units times the upper unipotent group to the upper triangular subgroup. Its inverse reads the diagonal and removes it by left multiplication. In these coordinates left translation by an upper triangular element translates the diagonal, and translates the unipotent coordinate on the left by an element depending on the diagonal. Both operations preserve the corresponding Haar measures; `MeasurePreserving.skew_product` therefore gives left invariance on the triangular subgroup. The coordinate homeomorphism transports positivity on open sets and finiteness on compact sets.

The real Iwasawa factorization in `RealIwasawa` shows that the triangular and orthogonal subgroups multiply onto the group. The compact factorization theorem then identifies the pushforward of the triangular and orthogonal Haar product with `μ` up to positive scale. Finally, `upperEntryProductMeasure_isHaar` identifies the pushforward from additive entry coordinates with the unipotent Haar measure used in the triangular subgroup.

## Provenance and scope

This is an internal integration lemma for the real principal-series matrix zeta integrals in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, pp. 30–31. The same triangular and compact factorization method is used over `ℂ` in the Library's `ComplexTriangularHaar`. No conversion to actual upper entries of `diag(t) u(x)` and no functional equation is asserted here; the row scaling in that conversion is a separate step.
