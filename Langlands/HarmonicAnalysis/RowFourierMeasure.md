# Row Fourier integrals with an explicit measure

This internal extension of `RowFourier` supports the coordinate measures in
Shahidi, *Fourier transforms of intertwining operators and Plancherel measures
for GL(n)* (1984), printed pages 76–77, measure items 3 and 5. The registered
source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Item 3 uses a product of coordinate measures `dx_i`, requires that product
to be self-dual for the conjugate-character dot-product kernel, and fixes
`dx_1 = dz`. It does not require the coordinate measures to be equal or
individually self-dual. Item 5 permits a matrix-coordinate factorization and
matches its first-column factors to the `dx_i`. The present unit supplies
the Fourier and product-measure interface needed to express those conditions;
it does not impose the first-coordinate or first-column equalities.

All declarations are in `Langlands.HarmonicAnalysis`.
`rowCoordinateMeasure μ` is the actual finite product of the supplied regular
additive Haar measures `μ i`, which may vary with `i : Fin d`. With sigma-finite
coordinate measures it is sigma-finite, additive Haar, and finite on compact
sets. Additive Haar invariance additionally requires measurable addition.
`rowCoordinateMeasure_box` evaluates any coordinate box as the product of its
coordinate masses. A constant family is exactly the existing `rowMeasure`.
These claims follow from Mathlib's finite product measure results.

Positive finite rescaling of the individual coordinate measures multiplies
the row measure by the product of the scale factors. This is proved by
uniqueness of product measure and the box formula.
`rowCoordinateMeasure_scale_of_prod_one` consequently preserves the actual
row measure when the product of the scales is one. This law exposes the
freedom in the coordinate factors without imposing a Fourier normalization
on any one factor.

`rowFourierIntegralWithMeasure ψ μ` is the scalar Bochner integral
of `ψ(sum_i x_i*y_i) * f(x)` against an actual supplied measure on `Fin d → F`.
The field is universe-polymorphic, and its topology and Borel structure are
explicit. This general raw definition retains the ordinary nonintegrable
Bochner convention on arbitrary functions.
For measures finite on compact sets, the integrand is integrable for every
Schwartz–Bruhat input: continuity of the character and pairing combines with
the continuous, compactly supported test function. Thus
`rowFourierTransformWithMeasure` is a genuine complex-linear map from the
test space to all complex functions, with linearity proved by integral
addition and scalar multiplication. Preservation of the test space is not
claimed. On `rowMeasure μ d`, both constructions agree with the existing
`rowFourierIntegral` and `rowFourierTransform`.

`IsRowSelfDualMeasure ψ μ` is a Prop-valued definition requiring convergence
of the second Fourier integral and that Fourier squared is reflection on
every Schwartz–Bruhat function. It is a condition on the entire measure `μ`.
It neither assumes nor proves existence of such a measure. On a constant
coordinate product it is equivalent by definition to `IsRowSelfDual ψ μ d`.
In particular, the source's vector normalization can be expressed by
`IsRowSelfDualMeasure (ψ.scale (-1)) (rowCoordinateMeasure dx)`.

The character-sign translation is proved explicitly.
`complex_scale_neg_one` identifies `(ψ.scale (-1)).complex x` with the
complex conjugate of `ψ.complex x`, using the additive character law and
its unit norm. The two integral translation lemmas identify the transform
for this scaled character with the conjugate-character integral and,
equivalently, the original plus-sign transform evaluated at `-y`.
These identities use the same supplied measure; they do not invoke a change
of variables or any Haar-normalization theorem.

The generality in the measure and the elementary product and integral laws
are internal foundations, not analytic theorems attributed to Shahidi.
This unit does not construct the other coupled measures, prove Fourier
inversion, relate the row measure to the matrix measure, or implement the
local coefficient or its comparison with the JPSS factor. In particular
it makes no claim that the matrix measure is self-dual.
