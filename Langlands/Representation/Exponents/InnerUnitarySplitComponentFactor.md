# Actual split-component factors for inner unitary Jacquet exponents

Worker 17. This derived construction concerns an actual outer parabolic of a
connected reductive group, its original rational Levi `L`, and an actual inner
parabolic of `L` with original rational Levi `M`. The original split components
are `A` of `L` and `B` of `M`. The ambient smooth representation satisfies
`IsNormalizedExponentTempered`.

The actual Levi-parabolic extension theorem supplies a fine ambient parabolic
with the same original inner Levi `M`. Ambient temperedness supplies a compatible
root presentation for this fine parabolic and the specified split component `B`.
The outer split component is central in `L`, so
`ParabolicRootPresentation.intermediateSplitComponentFactor` factors it through
`B`. The construction `innerSplitComponentFactor : A ⟶ B` chooses such a map.
Its composite through `B ⟶ M ⟶ L` is the original map `A ⟶ L`, on every test
scheme; `innerSplitComponentFactor_points` gives the corresponding equality on
rational points.

The last theorem applies the published central restriction of inner exponents
to this actual point factor. It gives zero normalized real part on `A`.
The inner normalized exponent has an open kernel; naturality of normalized real
parts under actual split-torus maps then identifies this zero real part with
`rationalCharacterRestrictReal` applied to the original inner exponent parameter.

No compatible point factor or presentation-existence premise is added:
the fine presentation is extracted from the ambient temperedness hypothesis.
The construction retains arbitrary field and carrier universes and the original
local-field, topology and actual parabolic data. It does not establish inner
presentation coverage, a comparison of root cones, or either remaining
temperedness or square-integrability proposition. Its provenance is composition
of the published actual extension and central restriction constructions with
the split-component factor and normalized real-part naturality laws; it is an
internal intermediate step for Renard VII.2.3.
