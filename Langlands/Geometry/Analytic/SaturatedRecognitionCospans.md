# Saturated recognition cospans and finite pointed chart pairs

This internal construction replaces any actual saturated strong cospan by
compatible full recognition maps with admissible recognized source charts.
The field universe and space universe are independent. All input, output,
source, base and localization objects have space and index universes equal to
the original space universe. Underlying spaces and ambient maps are literal.

`recognitionBase` is the full recognition of the original base presentation.
`recognitionSource f` selects precisely the recognized source charts of the
canonical saturation extension of `f` admitting a recognized target.
`recognitionMap f` retains its complete bounded pair system. Each constructed
atlas is full-domain closed. The forward source and base comparisons first
use the actual saturation comparison and then the canonical full-domain
recognition maps. Their ambient maps are identities and they are full strong
quasi-isomorphisms on every admissible chart pair.

`recognitionMap_square` proves equality of the two complete strong composites.
It combines the source-comparison identity for the recognized pair system
with the full bounded-map naturality of canonical saturation. Preservation
and reflection along source and target full quasi-isomorphisms then prove
`recognitionMap_strongEtale_iff`. The corresponding source and base comparison
isomorphisms live in the existing analytic localization; their naturality
square is the functorial image of this entire strong equality.

`HasPointedFiniteEtalePairs` is a Prop-valued interface for an actual strong
cospan. It quantifies every pair of prescribed ambient points with equal
image. Its witnesses are literal original source and common-base chart
indices, actual admissible bounded pullbacks and source spectrum points
charting to exactly those points. The first bounded map is finite Banach and
etale at its chosen point; their actual common-base spectrum images agree.

`recognitionMaps_hasPointedFiniteEtalePairs` proves this interface for the
recognition-selected cospan whenever the original first map is `strongEtale`.
That hypothesis tests its canonical extension, so the controlled all-pieces
finite selector applies directly. Take arbitrary original base and second
source charts through the two images and take whole-space neighborhoods.
The selected finite recognized pieces are literal original indices of the
new source atlases. Their bounded maps and chosen points are unchanged.

These results use the existing canonical saturation comparison, full-domain
quasi-isomorphism etale transport, actual localization, and controlled
recognized finite-pair selector. They transcribe no external theorem. They
do not assert that ordinary point pairs distinguish product points or
analytic morphisms, nor do they construct a global pullback or establish
its etale second projection. Those remain separate host-task obligations.

`recognitionBase A` abbreviates the existing `SaturatedAtlasPresentation.ofFullRecognition A.presentation`.
