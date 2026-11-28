# Composing local Čech–de Rham pullbacks

`LocalPullbacks.comp` composes two systems of algebra maps over the same
base ring \(R\), using the same ideal \(I\subset R\) and the same intermediate
affine cover. At each tuple and vertex the map is the composite through the
corresponding vertex of the intermediate cover. Restrictions commute with
the composite because they commute with each of its maps. Congruence follows
by inserting the composite using the first system at the second vertex
and the second system at the first vertex, then using preservation of the
extended ideal under algebra maps. These statements hold for any \(I\).

Assume \(I^2=0\) for the corrected cochain maps. With the Čech sign given by
the second vertex minus the first, the contraction for the composite
difference is the sum of two contractions obtained by inserting the
first-vertex map of the first system composed with the second-vertex map
of the second system. The first term contracts the one-form pulled back
at the second vertex by the second system. The other term applies the
first-vertex map of the first system to the second system's difference
contraction. The precomposition and postcomposition identities for
contractions give these terms. The restriction relation identifies the
pulled-back one-form on the overlap. On charts the one-form maps compose by
naturality of Kähler pullback. This gives `cochainOne_comp` for all degree-one
cochains.

When all three structure morphisms are smooth and separated and the three
affine covers are finite, `pullbackH1_comp` applies the cochain identity to
cocycle representatives and passes to the quotient by total boundaries.
These calculations follow from the affine homotopy and corrected cochain
formulas.
