# First fundamental Tits classes of actual norm-one groups

Let `A` be a central simple algebra of reduced degree `m ≥ 2` and let an
actual ground-field group isomorphism present `G` as `SL₁(A)`. With a matrix
splitting chart, this gives a numbering of the vertices of any supplied
Galois pinning. The numbering uses simple roots indexed by adjacent
coordinates on the diagonal torus of `SL_m`. The original column
representation of the chart has first fundamental highest weight in this
numbering.

The Brauer class of that first weight is `[A]` in the column convention. The
Tits algebra of an actual dual highest weight is computed by the opposite
chart, with class `−[A]`. The class of the last fundamental weight is also
`−[A]`: the two endpoint weights sum to the root from the first coordinate
to the last, so additivity and root vanishing give the sign. This argument
includes degree two, where both endpoints are the same simple vertex.

`normOneAbsoluteTitsNormalization` uses the constructed splitting chart over
the separable closure. The proof establishes vertex innerness for the supplied
pinning and uses the complete integral obstruction. It applies to all fields,
including imperfect fields and characteristics dividing `m`. The calculation
is an internal normalization of the Library's implementation of Tits's
construction in Theorem 3.3 and Corollary 3.5 of the 1971 paper.
