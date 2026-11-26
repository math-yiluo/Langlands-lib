# Undoing determinant normalization on the two leading real variables

This module is the real counterpart of the Library's `ComplexGapNormalizationShear`.

* `continuous_leadingScalar`: the scalar `leadingScalar k q y = exp(−∑ y_i / k) · 1` of `RealGapUnitDeterminant`
  depends continuously on `y`.
* `outerChange k q dual` replaces the leading matrix `g₁` of the outer coordinates by
  `leadingScalar(y)^{-1} · leadingSide dual g₁` (`outerChange_apply`).
* `normalizationShear t q dual` also translates the quotient point on the right by `leadingScalar(y)`
  (`normalizationShear_apply`).

`RealGapNormalizationShearStatement` (proved by `realGapNormalizationShear`): for Haar measures `η₁` on
`GL_{t+1}(ℝ)` and `κ` on the orthogonal group and σ-finite `νY`, `normalizationShear t q dual` preserves
`alternateGapMeasure t q a D νY η₁ κ`. For fixed tail logarithms the quotient measure is right invariant
(`D.compatible.right_invariant`) and `η₁` is left invariant and invariant under inverse transpose
(`Langlands.GodementJacquet.realHaar_measurePreserving_inverseTranspose`); Tonelli's theorem assembles
these fibrewise statements. The complex module uses the explicit complex Haar measure; here `η₁` is any
Haar measure.

This is an internal step of the convergence and Mellin analysis of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
