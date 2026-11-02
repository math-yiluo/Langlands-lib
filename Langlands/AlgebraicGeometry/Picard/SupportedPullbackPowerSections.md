# Supported sections of actual pulled-back powers

This internal helper supplies the tensor-power conversion in the proof of
fixed-bundle ampleness reflection. It uses the Library's actual tensor powers,
actual module pullback and section generation opens.

For a morphism `q : Y ⟶ X`, a line bundle `L` and exponents `n, m`,
`supportedPullbackTensorPowIso` first flattens the `m`-th power of the `n`-th
power of `q*L`, using `tensorPowMulIso`, and then applies the inverse of
`actualPullbackTensorPowIso`. Its target is the actual module pullback
`q*(L^(n*m))`.

`exists_vanishing_pullback_powerSection` starts with a section of a positive
power of `q*L` and a morphism `i : T ⟶ Y` from a quasi-compact scheme whose
inverse image of the section's generation open is empty. The support helper
`exists_pos_pullback_sectionPow_eq_zero` gives a positive power of this
section that vanishes after pullback along `i`. The constructed isomorphism
transports it to a section of `q*(L^r)`, with `r` positive.
`trivializationOpen_sectionPow` and `trivializationOpen_mapIso` show that its
whole generation open equals that of the initial section.
`pullbackSection_mapIso_eq_zero_iff` transports the vanishing condition.

`exists_vanishing_upstairs_section` applies this conversion in the field
base-change setting. The geometric basis helper supplies a point above `x`
and an upstairs section supported in the inverse image of `U`. The base change
of `closedComplementι U` is a closed immersion into the quasi-compact upstairs
scheme, so its source is quasi-compact. Commutativity of the pullback square
and the image formula for the closed complement make the inverse image of the
section's generation open empty. The preceding lemma then gives an actual
pulled-back positive-power section generating at the chosen point and vanishing
on this base-changed complement. This construction includes inseparable field
extensions, for which that source may be nonreduced.

This is derived content from the cited Library constructions and the companion
section-support helper. It imposes no field, separatedness, reducedness or
finite-type hypothesis and does not itself extract a downstairs section or prove
ampleness reflection.
