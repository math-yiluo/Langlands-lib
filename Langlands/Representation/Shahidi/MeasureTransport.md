# Weighted measure conversions in Shahidi's normalization

This unit implements two specific measure formulas from Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)* (1984), printed pages 76–77, measure items 2 and 5. The registered
source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
These formulas are ingredients of the source's coupled normalization, not a
complete definition of suitable measures for Theorem 5.1.

The declarations are in `Langlands.Shahidi`. They use an actual field, its
topology and Borel measurable structure, a real-valued absolute value, and
actual measures on its unit group or general linear group. Their elementary
measure identities need neither continuity nor a local-field normalization
of the supplied absolute value. No Haar property is assumed of the input
measure, and no Haar property is claimed of the output.

`fieldMeasureFromUnits abv μ` first weights the measure on `Fˣ` by
`ENNReal.ofReal (abv z)` and then pushes it forward along the inclusion
`Fˣ → F`. This realizes page 76's `dz = |z| d*z`. The `_apply` lemma states
its exact value on any measurable set as a nonnegative integral over the
inverse image. The `_smul` lemma proves that scaling the input measure scales
the output by the same extended nonnegative scalar. In a T1 field the
`_zero` lemma proves the resulting measure gives zero mass to `{0}`.

`matrixMeasureFromGeneralLinear n abv μ` weights the measure on `GL_n(F)` by
`ENNReal.ofReal (abv (det g)) ^ n` and pushes it forward along the actual
inclusion into the square matrix space. This realizes page 77's
`da = |det a|^n d*a`, with zero mass on the singular locus. It is defined at
every natural rank, including zero; the source application uses positive
rank. Its `_apply` and `_smul` lemmas have the same meanings as in the field
case. With a Hausdorff topological-ring structure, `_singular` proves the claimed zero mass on
singular matrices: that locus is measurable by continuity of the determinant
and has empty inverse image in `GL_n(F)`.

The proofs use the actual `Measure.map` and `Measure.withDensity` evaluation
and scalar laws. The inclusions are measurable because they are continuous
and the indicated spaces have Borel measurable structures. Thus there is no
postulated change-of-measure property or unidentified normalization constant.
The extension across the noninvertible locus is the explicit internal
implementation of the source's measure notation; identifying it as additive
Haar for normalized local-field data is a separate analytic obligation.

The construction does not fix the multiplicative measure of the center,
the measures on the lower-rank group and last-column unipotent subgroup,
the compact-group measure, or the Iwasawa product formula of pages 75–77.
It also does not identify the matrix measure with a product of a fixed
self-dual scalar measure: page 82 explicitly says the matrix measure need
not be self-dual. Those choices and compatibility relations, the shared
measure for the two Jacquet functionals, and the all-rank measure convention
remain obligations of the parent Shahidi framework. No existence theorem,
Fourier compatibility theorem, or gamma-factor comparison is assumed here.
