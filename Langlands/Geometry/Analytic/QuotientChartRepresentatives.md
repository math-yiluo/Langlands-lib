# Whole-chart strong representatives of quotient arrows

Author: Worker 36.

This internal construction extracts full strong representatives of an arbitrary
arrow in the actual source-refinement quotient on a locally refining family of
original whole chart domains. It uses the existing complete strong-map category,
source numerators, and domain inclusions. It introduces no additional assertion
from the original literature and assumes no global strong representative.

For a refining source selection `P` and an original-chart domain `S` whose every
contained original chart belongs to `P`, `selectedDomainFactor` constructs a
strong map from the full original presentation of `S` into the selected ambient
atlas. Its base map is the literal inclusion of the subset. Every admissible
bounded pullback is the original ambient restriction. Each source chart itself
is selected and therefore supplies a containing target chart. The existing
restriction identities prove compatibility.

`selectedDomainFactor_comp_inclusion` proves the complete strong factorization
triangle into the ambient presentation. For each source chart, compute the
saturated composite through its identical selected target chart. Both factors
are original identity restrictions; their composite is the original identity.
Full strong extensionality proves the triangle. When `S` is the whole image of
a selected chart, downward closure supplies the selection of every contained
original chart. `selectedChartFactor` is this special case.

The full original strong map between nested domain presentations, followed by a
strong map, is the direct source-domain restriction. The proof computes the
saturated composite through the identical original chart in the intermediate
domain and removes its bounded identity. Monicity of the quotient domain
inclusion then identifies `domainMap` with the image of that full strong
inclusion. Consequently `domainMap_comp_strong` identifies quotient restriction
with the image of the direct full strong restriction.

For a numerator `f` on `P`, the strong factorization triangle and the existing
denominator cancellation show that restriction of its quotient class to `S`
is the image of `selectedDomainFactor P S hS` followed by `f`.
`selectedChartFactor_comp_ι` gives this equation on every selected whole chart.
These equalities compare complete quotient arrows, not just their point maps.

`ChartRepresentation F` retains a downward-closed locally refining selection
of original charts, a full strong map on every selected whole chart domain,
and its equation with the corresponding restriction of `F`.
`nonempty_chartRepresentation` proves existence by quotient induction on an
actual numerator and the constructed chart factors. `chartRepresentation`
chooses the resulting local data. The selection's local refinement is part of
the constructed numerator data, rather than a new cover assumption.

The field may be trivially valued. No nonemptiness, reducedness, directedness,
or equality principle for seminorm-point maps is used. The field, ambient
space and chart-index universes are independent. This unit constructs local
strong representatives; arbitrary matching-family gluing, full analytic
identification, and the etale and equivariant sites remain separate obligations.
