# The ordinary and mixed factors on the normalized real gap chart

This module is the real counterpart of the Library's `ComplexGapOrdinarySeparation`;
`RealGapOrdinaryMellin` continues the same namespace.

* `leadingRestriction_retainedTail`: the leading restriction of a test by the retained matrix does not
  depend on the packed tail. `tailFactor_mul_whittaker` combines the tail factor and the translated
  Whittaker value into the triangular Fourier kernel of `RealGapTailExchange` (for `W` left equivariant
  under the character of `−a`). `character_retainedTail`: the retained matrix and its unit-determinant part
  have the same character value.
* For `dual : Bool`, `rectangularLeading` is `T.leading` or its rectangular transform, `squareLeading` is the
  leading restriction or its `realRectangularSchwartzFourier a`, and `sideCharacter dual c` is `c` or
  `c⁻¹`. `chartMultiplier` collects the character of the retained matrix and the weight
  `η(det h) · |det h|^{t/2}` of the leading side `h`; `norm_chartMultiplier` gives its norm
  `|det h|^{Re(exponent) + t/2}`.
* `comparisonChartKernel` is `normalizedWeightedKernel` for these factors, and `ordinarySeparatedKernel` the
  product of the retained coefficient, the ordinary smaller kernel `weightedOrdinary` of the translates,
  the square weight `realAdjacentMatrixWeight (sideCharacter dual c) (squareLeading …) 0` at the leading side
  and the second profile. `comparisonRectangleMeasure` is a point mass at zero (ordinary) or rectangle
  Haar measure (mixed); `ordinaryChartMeasure a η₁ κ` is `unitOuterMeasure × entryHaar`.

`RealGapOrdinarySeparationStatement` (proved by `realGapOrdinarySeparation`): for Haar `η₁`, `κ` and `W` in
`realUniformWhittakerModel (t+1+q) ds (−a)`, integrability of `comparisonChartKernel` for
`normalizedGapMeasure` gives integrability of `ordinarySeparatedKernel` on the quotient and
`ordinaryChartMeasure` and equality of the integrals. `integrable_ordinarySeparatedKernel` gives this
integrability for `V` in `realUniformWhittakerModel t es a` and measurable rapidly decaying profiles, from
`realGapNormalizedWeighted`.

## Proof

Unfolding the normalized kernel with `tailFactor_mul_whittaker` and `character_retainedTail` separates the
factor depending on the leading rectangle. On the ordinary side the point mass evaluates it at zero; on
the mixed side `realGapLeadingFourier`, for a retained matrix of absolute determinant one, integrates it to
the rectangular Fourier transform of the leading restriction. A permutation of the product measure and
Fubini give the identity.

These are the ordinary and mixed steps of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.3,
Lemma 10.3, p. 74, and (10.10), p. 76, in the absolutely convergent form of §10.4, Lemma 10.5, pp. 77–78.
