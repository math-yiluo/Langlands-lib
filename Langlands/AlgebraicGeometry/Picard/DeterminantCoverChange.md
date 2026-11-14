# Determinant comparisons across different open covers

For two actual finite frame systems of the same module sheaf and with the
same finite basis index type, this module constructs an isomorphism between
their determinant sheaves even when their open covers and chart index types
differ.

`refineCocycle_reindex` identifies the determinant cocycle of a selected
subfamily with the restriction of the original cocycle. The corresponding
actual generator frames give `reindexIso` whenever that subfamily covers.
Its forward and inverse maps preserve the selected generators.

`sumFrames` contains both frame systems. Applying `reindexIso` to each
inclusion and composing gives `coverChangeIso`. On an open inside one chart
from each cover, its action sends the first generator to the second
generator times the determinant of the first frame expressed in the second.
`coverChangeUnit_mul` proves multiplication of these mixed determinants.
`lineBundleCoverChangeIso` lifts the comparison to actual line bundles.
Both comparisons satisfy identity and composition as equalities of actual
isomorphisms. For identity, the determinant of a frame in itself is one.
For composition, restrict to opens inside a chart from each of the three
covers. Each source section is a scalar multiple of its local generator,
and the generator formula reduces the claim to mixed determinant
multiplication. The sheaf separation property then gives the global equality.

This is internal derived content using actual section bases, determinant
identities, and the published refinement and frame gluing constructions.
Varying rank, pullback coherence, and the parabolic polarization and its
ampleness remain separate obligations.
