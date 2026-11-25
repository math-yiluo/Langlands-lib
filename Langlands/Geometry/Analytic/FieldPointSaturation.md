# Base-field points and atlas saturation

This internal comparison proves that passing from an affinoid atlas to its
constructed saturation preserves its base-field-valued points and their
underlying points. It supports clause (3) of
`AffineAnalytificationRationalPointsStatement`. The base field is normed,
ultrametric and complete; the space and chart-index universes are independent.

The implementation adapts a rationality construction written for the proof of
`AffineAnalytificationRationalPointsStatement`. A character to the base field is determined by its
absolute value, by subtracting the scalar equal to its value. Therefore a
base-field-valued point is determined by its underlying point.

To extend a rational character to a contained chart, the proof tests the
restriction universal property on the zero-variable affinoid algebra over the
base field. The original character, followed by scalar inclusion in this test
algebra, has constant spectrum image. This follows because every bounded
multiplicative seminorm on a field is its norm, as seen using a nonzero element
and its inverse. The resulting factorization followed by evaluation in the base
field gives the required contained-chart character.

Every saturated chart lies in an original chart. The whole original chart is
also a saturated chart, so the preceding extension gives rationality on every
saturated chart. Conversely, restriction from a saturated whole chart gives
rationality in the original chart. Character uniqueness automatically gives
restriction compatibility. The maps `toSaturated` and `ofSaturated` keep the
underlying point literally fixed, and point uniqueness proves both inverse
laws of `saturationEquiv`.

This is a derived proof from the published atlas, full-domain universal
properties, and all-chart field-point definitions. It assumes neither a
completed-residue-field comparison nor a general field-valued domain extension
theorem. Its use for rational points is the saturation step in the affine
comparison modeled on Berkovich 1990, Theorem 3.4.1 and Remark 3.4.2, and
Conrad–Temkin 2009, Example 2.3.2; those source comparisons are documented in
the published target's Markdown.

The field-spectrum evaluation identity is reused directly from
`BanachSpectrum.field_apply` in `Spectrum.Properties`.
