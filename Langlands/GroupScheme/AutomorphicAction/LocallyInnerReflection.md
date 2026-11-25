# Fppf reflection of local innerness

This internal module proves that `IsFppfLocallyInner` and
`IsFppfInnerEquivalent` can be checked after one flat, surjective, locally
finitely presented base change. The schemes, including all relative tests,
are arbitrary.

For `IsFppfLocallyInner.of_baseChange`, the given local conjugator lives over
an fppf cover of the new base. Compose this cover with the original fppf
map and project the conjugator using the published multiplicative
`baseChangePointsEquiv`. For every test over the composite cover,
`LocalGroupIso.coverTest` gives a test over the new base, so the given
all-refinement conjugation equation applies. The multiplicative point
equivalence preserves conjugation and commutes with the given actual
automorphism. Its projection is therefore the required conjugation equation
on the original base.

The forward base-change preservation theorem from `LocallyInnerTransport`
gives `isFppfLocallyInner_baseChange_iff`. Applying this equivalence to
the source discrepancy of two actual isomorphisms proves
`IsFppfInnerEquivalent.of_baseChange` and
`isFppfInnerEquivalent_baseChange_iff`.

`fppfInnerComparisonSetoid` packages the previously proved equivalence
relation on actual comparisons. Its quotient
`FppfInnerComparisonClass G H` is the type of those local-inner classes.
Base change defines a map of these quotients because it preserves inner
equivalence. The reflection theorem shows that this map is injective for
an fppf cover. This is a separatedness assertion for supplied actual
comparisons; no effective descent of arbitrary families of classes is claimed.

These are derived transport and cover-composition facts. They assert no
existence of pinning normalization or coherent pinned comparisons.
