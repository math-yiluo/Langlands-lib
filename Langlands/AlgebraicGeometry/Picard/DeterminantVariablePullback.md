# Pullback of determinant frames of variable finite rank

This derived construction applies to actual finite local frame systems of a
module sheaf on an arbitrary scheme. The finite rank may vary with the chart.
For any scheme morphism, `pullbackFrames` constructs actual frames of the
pulled-back module on the inverse-image opens, retaining each finite rank.

A frame vector defines an actual local homomorphism from the structure sheaf.
The basis expansion identity gives its expression as a finite linear combination
of another chart's generators. The local-hom pullback is additive and respects
scalars through the structure-sheaf ring map. Applying it to this expansion
and comparing coordinates proves `basis_repr_pullback`, with potentially
different finite ranks on the two charts.

`unit_pullback` applies the mixed finite-basis determinant ring-map theorem to
these actual coordinate identities. Therefore the determinant cocycle of the
pulled-back frames is the actual pulled-back determinant cocycle. The existing
cocycle pullback construction and this equality give `pullbackIso` between the
actual pullback of the determinant sheaf and the determinant sheaf constructed
from the pulled-back frames. Its generator formula identifies the pullback of
each original generator with the corresponding new generator.

When the original chart opens cover, these sheaf isomorphisms lift to
`lineBundlePullbackIso` between actual line bundles. This proof extends the
imported fixed-rank determinant pullback argument using actual finite basis
coordinates and mixed determinants. The scheme and cover index types share
one universe. No affineness, quasi-compactness or constant-rank hypothesis is
used. The supplied frames and covering property remain inputs; frame existence,
pullback identity/composition coherence and parabolic polarization remain
separate obligations.
