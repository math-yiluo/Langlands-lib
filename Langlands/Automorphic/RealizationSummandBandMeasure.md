# The determinant band and the positive-central quotient of GLₙ

This is an internal comparison for the proof of
`GeneralLinearCuspidalRealizationSummandStatement`. It relates the Library's determinant-band
integrability results to the Library's particular quotient measure; no independent measure
normalization or square-integrability input on the positive-central quotient is assumed.

Write `p` for `projection`, from the principal rational quotient to the positive-central
rational quotient `Q`. The determinant character evaluated on adelic points is the matrix
determinant, by `characterOnAffineMatrices_determinantCharacter` in
`Langlands/GroupScheme/Rational/GeneralLinearCharacterAdapters.lean`. Thus the norm-one
subgroup for algebraic characters has determinant norm one. Under the decomposition of
`Langlands/Global/AdelicSplitCenterHaar.lean`, the determinant norm depends only on the positive
torus coordinate, and `p` depends only on the norm-one coordinate.

The proof pulls back the chosen Borel norm-one fundamental domain by the norm-one factor map.
This is a fundamental domain for the full rational subgroup: the norm-one projection is a
homomorphism that identifies the rational subgroup with its norm-one copy. In product
coordinates, the preimage of a measurable subset of `Q`, intersected with the band and this
domain, is a rectangle. Its first factor is the positive band, defined by `1 < |det| < 2` on
the positive coordinate; its second factor is the preimage of the subset in the norm-one
fundamental domain. With `map_normalizedPositiveHaarMeasure_prod` and the quotient-measure
formulas, the rectangle formula gives `map_bandMeasure`:

`map p (principal quotient Haar restricted to the band) = bandConstant • quotient Haar on Q`.

Here `bandConstant` is the normalized positive Haar measure of the first factor. In positive
rank the band is open and nonempty (a scalar adelic point has determinant norm `3/2`), so the
constant cannot be zero. A nonzero continuous function on `Q` whose pullback belongs to
band `L²` forces the constant to be finite, since quotient Haar charges nonempty opens and
hence the function has nonzero `L²` seminorm. The remaining lemmas transfer integrals and
square integrability using the pushforward identity.
