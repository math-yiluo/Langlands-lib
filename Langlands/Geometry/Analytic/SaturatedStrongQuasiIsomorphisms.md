# Full quasi-isomorphisms on saturated affinoid atlases

This unit is an internal construction on the actual category
`SaturatedAtlasPresentation`, using its original all-admissible-pair
`StrongHom` morphisms. It retains the existing definition `IsQuasiIso`:
an ambient homeomorphism together with full affinoid-domain representation
by every admissible original bounded pullback. It uses the already proved
full domain composition, arbitrary chart-change representation, exact
bounded-chain recovery, and saturated-source extensionality.

`mapChartImage_chainPullback` identifies the ambient image of an actual
bounded pullback chain with the image of its original source chart under
the literal composite continuous map. Its proof is the original chain
chart equation followed by the elementary range-of-composition identity.

`IsQuasiIso.saturatedComp` proves closure under the constructed strong
composition. Choose a containing intermediate chart and then a containing
final chart. The two original full representations compose because the
outer spectrum map is embedded, as follows from the ambient homeomorphism
and the original chart embeddings. The resulting bounded map fully
represents a domain in this final chart. Arbitrary chart-change
representation transports it to each requested admissible final chart.
The exact chain-change formula identifies that map with the actual
composite pullback. This proves full representation, including bounded
factorization and uniqueness for every presented affinoid test, at every
admissible pair. The source and intermediate atlases contain all their
local full domains; the final atlas is arbitrary. No directedness
is assumed.

`IsQuasiIso.cancel_saturatedComp` proves right cancellation. Injectivity of
the ambient homeomorphism gives equality of the original continuous maps.
At a selected admissible pair for each source chart, exact chain recovery
turns the equality after composition into equality of bounded composites
with a representing structural map. Its full uniqueness property cancels
that map. Saturated-source extensionality then gives equality of the entire
strong morphisms. The equivalence `saturatedComp_eq_iff` records this
cancellation in both directions. The source and intermediate atlases are
saturated, and the final atlas remains arbitrary.

In the actual saturated category, `quasiIsomorphisms` is the resulting
morphism property. Its `IsMultiplicative` instance combines the original
identity theorem with the new composition theorem. `mono_of_isQuasiIso`
and `postcompQuasiIsoEmbedding` give the categorical cancellation
consequences, with the embedding using the actual category composition.

This unit supplies neither a strong inverse for every quasi-isomorphism
nor a localization category. Whole-atlas extension and analytic sites
remain separate construction obligations.
