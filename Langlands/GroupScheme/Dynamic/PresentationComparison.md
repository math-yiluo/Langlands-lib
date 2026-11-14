# Comparisons for prescribed dynamic presentations

These are internal comparisons for composing pointed cocharacter lifts and
supplied dynamic presentations, using the published dynamic base-change and
isomorphism functoriality, the canonical pullback comparisons, and the
multiplicative-group tower identity. No new literature assertion is introduced.

Normalized cocharacter pullback respects composition with a subgroup inclusion
and the canonical pullback tower comparison. An ambient isomorphism preserves
and reflects equality between a subgroup range and a dynamic parabolic.
Consequently exact recovery of a cocharacter inside a subgroup recovers its
ambient composite and the corresponding presentation of the iterated fibre.
The statements concern homomorphisms and subgroup images on all test schemes;
they impose no closedness hypothesis.

`pullbackCocharacter p q r h χ` pulls an actual cocharacter over `T` back along
`q : U → T` and then composes with the canonical comparison from the iterated
pullback along `p : T → S` to the direct pullback along `r : U → S`, where
`h : q ≫ p = r`. Its source is the actual multiplicative group over `U`.
`pullbackCocharacter_presents` proves that a supplied presentation of a subgroup
over `T` gives a presentation of the directly pulled-back subgroup over `U`.

`pullbackComparison_tower` establishes coherence around a three-step pullback
tower. Its proof compares morphisms into the direct pullback: both have the
same projection to the original group and the same structure map to the base,
so pullback extensionality identifies them. `pullbackCocharacter_recovers`
combines that coherence with normalized cocharacter tower compatibility. Thus
restriction along an additional neighbourhood does not change the prescribed
value at any supplied scheme-valued point, after the specified canonical
comparisons. These comparisons do not construct a presentation that was not
already supplied.
