# Rank-one stalk spreading on arbitrary schemes

This internal derived module proves that a rank-one actual stalk of a locally
finitely presented module sheaf on any scheme has an actual trivializing open
neighbourhood. It works in every universe, without noetherian hypotheses.

Local finite presentation supplies an open containing the given point with an
actual finite global presentation of the restricted sheaf. An affine spectrum
chart of that open supplies a point mapping to the original point. Pullback of
the finite presentation and the actual restriction-composition comparisons give
a finite presentation of the original sheaf restricted to the composite open
immersion. In particular its actual global sections on that spectrum are
finitely presented.

Two further internal lemmas establish finite presentation of actual affine
stalks. The associated-sheaf stalk is a module localization; regarding that
localization as scalar extension preserves finite presentation over the actual
local ring. For a quasi-coherent sheaf with finitely presented affine global
sections, canonical scalar transport to the coordinate ring and the actual
`fromTildeΓ` isomorphism give the same conclusion. An explicitly typed
associated-sheaf isomorphism keeps the canonical scalar actions fixed.

For the general spreading theorem, the linear restriction-stalk comparison
transports the given local-ring-linear equivalence to the chosen spectrum
chart. The affine spreading result puts the chart point in the restricted
sheaf's rank-one locus. The equality describing that locus under an open
restriction returns membership of the original point in the original sheaf's
rank-one locus.

`rankOneTrivializingNeighbourhood` uses classical choice to select an actual
open containing the original point, together with existence of an isomorphism
from the restricted sheaf to the structure module. It asserts no compatibility
between this choice and the input stalk equivalence.

All these results compose the imported Library and Mathlib constructions,
including the actual restriction-stalk comparisons. They introduce no
additional literature claim. The full Picard-stack atlas and reflection from a
base-changed fibre remain separate obligations.
