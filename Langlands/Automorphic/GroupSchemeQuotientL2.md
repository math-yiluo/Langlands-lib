# Continuous functions in the actual positive-central quotient L² space

This internal construction uses the existing
`PositiveRealTorus.PositiveRationalQuotient F G T i`, namely the actual left
homogeneous quotient of the actual adelic point group by the subgroup generated
by the intrinsic positive image of the supplied torus map `i` and the principal
rational subgroup. The number field is arbitrary, and the torus and its map are
actual group schemes and a group-scheme morphism. No assertion that the supplied
torus is the greatest rational split center is made here.

For any measure `measureQ` on that quotient, `QuotientL2` is literally `Lp ℂ 2 measureQ`.
`continuousL2Submodule` consists of continuous complex-valued functions satisfying
`MemLp` with exponent two. `continuousL2ToLp` is the complex-linear map obtained
by the pinned Mathlib `MemLp.toLp` construction; its representative agrees almost
everywhere with the original function. If every nonempty open set has positive
measure, equality of its images implies equality of the original continuous
functions: almost-everywhere equality and continuity give equality everywhere.
The construction requires neither a finite-volume premise nor boundedness.

For affine `G`, the positive right action on continuous quotient functions is
`R(g)f(q) = f(qg)`. Pullback through the actual quotient map is an injective
complex-linear map into the existing `ContinuousRationalFunctions F G`.
Rational left invariance follows from the inclusion of the principal subgroup;
continuity follows from the continuous quotient projection. Surjectivity of the
projection proves injectivity of pullback. The pullback intertwines the unchanged
positive right action on the existing rational function carrier.

`QuotientMeasureRightInvariant` explicitly requires that every actual right
translation preserve `measureQ`. Under this hypothesis, `quotientL2RightTranslate`
uses Mathlib's measure-preserving composition isometry on the actual `Lp`.
Its almost-everywhere formula is positive right pullback. The identity and
multiplication laws follow from the corresponding actual quotient maps and
contravariant composition of pullback; they give `quotientL2RightAction`.
Continuous square-integrable functions form a subrepresentation under the
same hypothesis, and passing to null classes intertwines these two actions.

The canonical specialization uses exactly the already constructed
`positiveRationalQuotientHaarMeasure`, with its existing normalization.
It retains affineness, local finite type, the actual character restriction's
injectivity and finite-index image, a finite splitting of the supplied torus,
centrality of the actual map, and right invariance of the fixed norm-one Haar
measure. The existing quotient-measure theorem supplies right invariance.
The existing compatible norm-one quotient measure is positive on nonempty open
sets by `QuotientIntegration.IsCompatible.isOpenPosMeasure`; the actual quotient
homeomorphism transfers this positivity to the canonical measure. Consequently
the continuous realization is faithful for that measure.

Provenance is internal: the construction combines the existing actual quotient,
the original continuous rational function carrier and quotient Haar measure
with pinned Mathlib's square-integrable null classes and measure-preserving
composition. It does not assert cuspidal square integrability, density,
closedness, smooth-vector comparison, general Haar unimodularity, reduction,
finite volume, or identification of the greatest rational split center.
Those remain separate obligations; no abstract Hilbert model is supplied or
assumed.
