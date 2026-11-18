# Ground field extension of rational charts

This module extends a rational chart of a presented `K`-affinoid algebra `A`
across a field extension `L/K` and compares the result with the ground field
extension of the chart algebra. It supplies the rational case of
`GroundFieldExtension.domainPreservation`. All declarations live in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension`.

`K` and `L` are ultrametric normed fields with `NormedAlgebra K L`, possibly in
different universes. The comparison part also assumes `[CompleteSpace L]`,
because the bounded functoriality `map` of ground field extension needs it.
The construction allows arbitrary positive radii, including over trivially
valued fields.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Remark 2.2.2(ii) (printed p. 28) gives the rational presentation with
positive radii. The proof of Proposition 2.2.4 (printed p. 29) uses the
representation of the inverse image of an affinoid domain after extension to
a field over which the algebras are strictly affinoid. This module proves the
rational case of that base change property for the Library's coefficient
extension `algebra K L A`. The chart and comparison maps are internal
constructions from the two presentation universal properties.
Registered source `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.

## The extended rational chart

- `extendSeries K L h` is the coefficient extension of a weighted series `h`
  over `K` with polyradius that of `A` to a weighted series over `L` with the
  same polyradius (the Library's `mapCoefficientsAlgHom` along
  `coefficientMap K L`).
- `presentationMap_extendSeries` identifies the class of `extendSeries K L h`
  in `A_L = algebra K L A` with `iota K L A` of the class of `h` in `A`.
- `generatesUnitIdeal_extend` shows that the coefficient extensions of the
  denominator and numerators of `d` generate the unit ideal of `A_L`. The
  proof maps the unit ideal along `ι` and uses `Ideal.map_span`.
- `rationalChart K L d : RationalChart L (algebra K L A)` has the same arity
  and radii as `d`, denominator `extendSeries K L d.denominator` and numerators
  `extendSeries K L (d.numerators j)`. `arity_rationalChart` records the
  arity.
- `locus_rationalChart` identifies the locus of `rationalChart K L d` with the
  preimage of `d.locus` under `spectrumProjection K L A`. The inequalities for
  the extended chart evaluate points on the images under `ι` of the original
  denominator and numerator classes.

## Comparison of chart algebras

Fix `d : RationalChart K A` and write `d_L = rationalChart K L d`.

- `chartFraction K d j` is the `j`-th fraction coordinate of `d.algebra`, and
  `chartFraction_equation` is its defining equation
  `baseMap(denominator) * fraction j = baseMap(numerator j)`.
- `instNormedAlgebraRationalChart` and `instIsScalarTowerRationalChart` regard
  `d_L.algebra` as a normed `K`-algebra through `K → L`.
- `extendedFraction K L d j` is the `j`-th fraction coordinate of `d_L`.
  `extendedFraction_hasBoundedMonomials` gives the weighted monomial bound with
  constant `1`, from the norm bound on fraction coordinates and
  `monomialValue_norm_le_weight`.
- `extendedBase K L d` is the bounded `K`-algebra map
  `A → A_L → d_L.algebra`, and `extendedBase_fraction_equation` states the
  fraction equations for it.
- `baseFraction K L d j` is the image `ι (chartFraction K d j)` in
  `algebra K L d.algebra`. `baseFraction_hasBoundedMonomials` is the weighted
  monomial bound for these images (Library lemma
  `RationalPresentation.hasBoundedMonomials_map_fraction`).

From here on `L` is complete.

- `toExtendedChart K L d : d.algebra → d_L.algebra` is the bounded `K`-algebra
  map given by the universal property of the rational presentation of
  `d.algebra` (`RationalPresentation.liftFromBase`) applied to `extendedBase`
  and the extended fraction coordinates. `toExtendedChart_baseMap` and
  `toExtendedChart_fraction` are its values on the base and on the fractions.
- `forward K L d : algebra K L d.algebra → d_L.algebra` is the bounded
  `L`-algebra map obtained from `toExtendedChart` by the universal property
  `lift` of ground field extension. `forward_iota` gives its value on the
  image of `ι`.
- `map_fraction_equation` shows that `baseFraction` satisfies the fraction
  equations of `d_L` relative to `map K L d.baseMap`. The proof rewrites both
  sides with `presentationMap_extendSeries` and `map_iota` and applies `ι` to
  `chartFraction_equation`.
- `backward K L d : d_L.algebra → algebra K L d.algebra` is the bounded
  `L`-algebra map given by the rational-presentation universal property of
  `d_L` applied to `map K L d.baseMap` and the images `baseFraction`.
  `backward_comp_baseMap`, `backward_baseMap` and `backward_fraction` are its
  values on the base and on the fractions.
- `backward_comp_forward` and `forward_comp_backward` are the two inverse laws.
  The uniqueness parts of the universal properties `hom_ext`
  for ground field extension and `RationalPresentation.hom_ext_base_fraction`
  for rational presentations reduce it to values on `ι` of the base, which
  agree by `map_iota` and the base map identities, and values on fractions, which
  agree by the identities for the images of fraction coordinates. `backward_forward` and
  `forward_backward` are the pointwise forms.
- `chartEquiv K L d` is the bounded `L`-algebra equivalence
  `d_L.algebra ≃ algebra K L d.algebra` with forward map `backward` and
  inverse `forward`. `chartEquiv_comp_baseMap` states that it carries
  `d_L.baseMap` to `map K L d.baseMap`.

## Consequences

- `represents_map_baseMap` proves
  `Represents L (map K L d.baseMap) (spectrumProjection K L A ⁻¹' d.locus)`.
  The extended chart represents its locus (`RationalChart.represents`), which
  is definitionally the stated preimage (`locus_rationalChart`), and
  post-composition
  with the equivalence `chartEquiv` (`Represents.postcomp_equiv`) together with
  `chartEquiv_comp_baseMap` transports the statement to `map K L d.baseMap`.
  The universal property holds against every presented `L`-affinoid test
  algebra.
- `spectrumMap_spectrumHomeomorph` shows that the spectrum map of `d_L` composed
  with the spectrum homeomorphism of `chartEquiv` equals the spectrum map
  `BanachSpectrum.comap` of `map K L d.baseMap`.
- `comap_map_baseMap_injective` follows from this factorization, injectivity of
  spectrum maps of rational charts (`RationalChart.spectrumMap_injective`) and
  injectivity of the spectrum homeomorphism.
