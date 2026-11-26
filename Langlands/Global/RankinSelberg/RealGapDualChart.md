# The real dual triangular Haar chart

This module is the real counterpart of the Library's `ComplexGapDualChart`. Notation as in
`RealGapUnitDeterminant`: `n = k + q + 1`, `ι` is the inverse transpose `g ↦ ᵗg⁻¹` of `GL_n(ℝ)` and
`ι₁` that of `GL_k(ℝ)`, and `w = tailWeyl k (q+1)` (see `RealGapWeylRestriction`).

* `reverseTranspose X` sends a `k × q` matrix `X` to the `q × k` matrix with entries
  `X_{j, q-1-i}`, its transpose with the rows reversed. `measurePreserving_reverseTranspose`: it carries
  `rectangularMeasure μ k q` to `rectangularMeasure μ q k`.
* `extendLower X` appends a zero last row to a `q × k` matrix, and `lowerShear X = [[1, 0], [X, 1]]`
  for a `(q+1) × k` matrix `X`. `lowerShear_mul`, `lowerShear_zero`, `lowerShear_inv` and
  `determinant_lowerShear` record that this is an additive embedding with determinant one.
* `retainedTail p Z = unitRetained p · packedTail 0 Z`; `normalizedAbs_retainedTail`: for `0 < k`
  its determinant has absolute value one.
* `inverseTranspose_rankInclusion`: `ι(diag(h, 1)) = diag(ι₁ h, 1)`;
  `tailWeyl_commutes_rankInclusion`: `w` commutes with `diag(h, 1)`.
* `dualRetained p Z = ι(retainedTail p Z) · w`, and the dual chart is
  `dualChart (p, (X, Z)) = dualRetained p Z · lowerShear(-extendLower X) · diag(ι₁ g₁, 1)`, with `g₁` the
  leading group variable of `p`. `measurable_dualChart`: it is measurable.

The key identity (a private lemma) is `ι(unitDeterminantChart (p, (X, Z))) · w =
dualChart (p, (reverseTranspose X, Z))`. The unit-determinant chart factors as
`retainedTail p Z · packedTail (laterRectangle X) 1 · diag(g₁, 1)`. Inverse transpose sends the upper
rectangle `laterRectangle X` to the negative of its transpose in the lower block. Conjugation by `w`
reverses its rows and moves its zero row, which comes from the zero first column of `laterRectangle X`,
to the last position.

`RealGapDualChartStatement` (proved by `realGapDualChart`): for `0 < k`, an additive Haar measure `μ`
on `ℝ`, Haar measures `η` on `GL_n(ℝ)` and `η₁` on `GL_k(ℝ)`, and an inversion-invariant Haar measure
`κ` on the orthogonal group, there is one `c > 0` with

`η = c • map unitDeterminantChart (unitOuterMeasure k q μ η₁ κ × (rectangularMeasure μ k q × entryHaar μ (q+1)))`

and

`η = c • map dualChart (unitOuterMeasure k q μ η₁ κ × (rectangularMeasure μ q k × entryHaar μ (q+1)))`.

The first equation is `realGapUnitDeterminant`. For the second, `g ↦ ι(g) · w` preserves `η`, since
inverse transpose preserves every real general linear Haar measure
(`Langlands.GodementJacquet.realHaar_measurePreserving_inverseTranspose`) and Haar measures on
`GL_n(ℝ)` are right invariant. Pushing the first equation forward by this map and using the key
identity and `measurePreserving_reverseTranspose` gives the second with the same constant. This is the
change of chart between (10.8) and (10.9) in Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§10.3.
