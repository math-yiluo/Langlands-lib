# The leading Haar measure in the real normalized gap chart

This module is the real counterpart of the Library's `ComplexGapLeadingHaar`. Notation as in
`RealGapUnitDeterminant`: an outer point `p` consists of the leading matrix `h ∈ GL_k(ℝ)`, the tail
logarithms `y ∈ ℝ^{q+1}`, an orthogonal matrix and the first rectangular column `x ∈ ℝ^k`.

* `Retained k q` is the type of the data `((y, v), x)` without the leading matrix. `splitOuter` is the
  measurable equivalence `p ↦ (h, ((y, v), x))`, and `outerWithLeading h r` its inverse
  (`splitOuter_apply`, `splitOuter_symm_apply`).
* `retainedTail_outerWithLeading`: the retained matrix `retainedTail p Z` of `RealGapDualChart` does not
  depend on the leading matrix.
* `retainedMeasure k q μ κ` is the product of the log-diagonal measure with the normalization density
  `normalizationWeight`, the measure `κ` on the orthogonal group and the row measure of `μ` on `ℝ^k`;
  `sigmaFinite_retainedMeasure` records that it is σ-finite when `κ` is a Haar measure (hence finite,
  the orthogonal group being compact).

`RealGapLeadingHaarStatement` (proved by `realGapLeadingHaar`): for an additive Haar measure `μ` on `ℝ`
and Haar measures `η₁` on `GL_k(ℝ)` and `κ` on the orthogonal group, `splitOuter` carries
`unitOuterMeasure k q μ η₁ κ` to `η₁ × retainedMeasure k q μ κ`.

The proof moves the normalization density into the log-diagonal factor (`prod_withDensity_right`,
`prod_withDensity_left`) and then reassociates the product. The module also records two measurable
equivalences of triple products, `interchangeMiddle : (A × C) × B ≃ A × (B × C)` and
`interchangeFirst : A × (B × C) ≃ B × (A × C)`, used to integrate the complementary rectangle first.
`measurePreserving_interchangeMiddle` and `measurePreserving_interchangeFirst`: when all three factor
measures are s-finite, they carry the corresponding product measures to each other.
These measure identities implement the separate integration over the leading variable in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §10.4.
