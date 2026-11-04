# Integer normalization on the actual maximal unramified field

Worker 60. This derived adapter uses the existing actual
`LocalGalois.Separable.inertiaFixedField F` and its published induced spectral
valuation. The base field has arbitrary universe and characteristic, with the
existing nonarchimedean local-field structures. No local-field, completeness,
or local compactness instance on the infinite fixed field is used.

Write \(K=\operatorname{inertiaFixedField}(F)\). The relation on \(K\) used
internally is exactly
`ValuativeRel.ofValuation (fixedFieldValued F).v`. The ordered value-group
isomorphism `valueGroupEquiv F` is the inverse of
`fixedFieldValueGroupEquiv F (fixedFieldValuesFromBase F)` followed by
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F`. In particular, value
attainment is supplied by the published proof, rather than a new hypothesis.
The definition `valuation F` maps the intrinsic valuation through this
isomorphism and has codomain `WithZero (Multiplicative ℤ)`.

The intrinsic valuation is onto and the value-group map is an isomorphism,
so `valuation_surjective` proves surjectivity. The canonical value-group
map takes a base valuation to the valuation of its image in \(K\). Applying
the inverse proves `valuation_base` and the equality of valuations
`valuation_comap_base`: restriction to \(F\) is exactly
`FML.normalizedMultiplicativeValuation F`, including zero and the chosen
integer normalization.

The ordered isomorphism preserves all valuation comparisons.
`valuation_isEquiv` proves equivalence with the published
`fixedFieldValuation F`; consequently `valuationSubring_eq` identifies its
valuation subring with the actual `fixedFieldIntegers F`. The ring
isomorphism `integersEquiv F` has the same image in \(K\), as
`coe_integersEquiv` proves.

The source-positive unit order is the generic `IntegerValuation.orderUnits`:
restrict to units, identify the nonzero multiplicative integer values, and
invert. Its additive form is \(-\log(v(a))\). `orderUnits_base`,
`orderUnits_comp_base`, and `orderUnits_base_eq_fieldOrderUnits` prove that
this order on \(K\) restricts to the existing base order, while `order_base`
proves the corresponding real-valued comparison.

The original motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Chapter 7 opening (PDF pp. 266–267), Chapter 8
opening (PDF p. 314, defining the maximal unramified field and its integer
ring), and §8.3 opening (PDF p. 326). The source-positive sign follows Notation 2.6.15 and
Lemmas 2.6.16–17 (printed pp. 102–103 / PDF pp. 133–134), with the positive
character-valuation formula in the authors' 1 November 2024 corrections,
PDF p. 25. Their corrections at pp. 33 and 37–38 retain additional
apartment and residue hypotheses for later geometric and model conclusions.
The value-group construction here is derived from the published arithmetic
and Mathlib's intrinsic value-group APIs, rather than a claimed transcription
of a separate source theorem.

This unit constructs the valuation and comparison maps. It supplies no
root-datum apartment or V6 data and asserts no inhabitance of building data,
AS5, V7, building existence, compactness, integral-model existence, or
unramified descent.
