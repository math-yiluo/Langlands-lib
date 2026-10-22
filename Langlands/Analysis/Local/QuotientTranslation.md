# Compact tests for quotient-measure invariance and nonzeroness

This internal helper unit supplies concrete inputs for the published
`measureOfPositiveAveraging_ne_zero` and `measureOfPositiveAveraging_preserving`
results in `QuotientFunctional`. Worker 112 proposed these interfaces; Worker 113
implemented the unit. Its only project import is the unchanged `QuotientMeasure`
API.

For any locally compact Hausdorff space with a Borel measurable structure,
`exists_compact_integral_ne_zero` proves that a nonzero regular measure has a
real compactly supported continuous test function with nonzero integral.
The proof supposes that every such integral vanishes and applies Mathlib's
`Measure.ext_of_integral_eq_on_compactlySupported` to the measure and the zero
measure. Regularity then forces the measure to be zero, a contradiction.
No group structure, countability, or Haar hypothesis is needed for this result.

For a topological group, `compactRightTranslate g` is the real linear map
on compactly supported continuous functions defined by
`compactRightTranslate g f x = f (x * g)`. It is Mathlib's compact-map
precomposition along the homeomorphism of right multiplication. That
homeomorphism is cocompact, so precomposition preserves compact support.
`compactRightTranslate_apply` records the definitional evaluation formula.

With a measurable multiplication and a right-invariant measure,
`integral_compactRightTranslate` proves equality of the translated and original
integrals using Mathlib's `integral_mul_right_eq_self`. This identity uses the
total Bochner integral and does not require a separate integrability hypothesis.

Finally, `compactAveraging_rightTranslate` takes any map
`P : C_c(G, ℝ) → C_c(LeftQuotient H, ℝ)` satisfying the exact formula
`P f (H x) = ∫ h : H, f (h.val * x) ∂μH`. It proves
`P (compactRightTranslate g f) q = P f (rightTranslate H g q)`.
Quotient induction reduces this assertion to the representative formula;
associativity identifies the two integrands pointwise. This implication needs
no algebraic property of `P`, no invariance of `μH`, and no integrability
hypothesis beyond the stated representative formula.

The construction is derived directly from the published quotient convention
and the named pinned Mathlib results, rather than an external source claim.
It supplies neither an averaging map nor a quotient measure. The full
`CompatibleMeasureExists` theorem remains a separate obligation.
