# Connected residue fibres of group schemes

This internal helper defines `HasConnectedResidueFibres G` by connectedness of
the actual base changes of a group scheme to the canonical residue fields of
its base. This is the connected-fibre hypothesis appearing in the published
`MultiplicativeTypeFibrewiseCentralityStatement`.

For a group scheme, this condition is equivalent to geometric connectedness of
its structure morphism. Each canonical fibre is itself a group scheme over its
residue field. Its unit is a rational section, so the published
`Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section` makes
that connected fibre geometrically connected. Mathlib's criterion
`GeometricallyConnected.iff_geometricallyConnected_fiber` then proves geometric
connectedness of the original structure morphism. The reverse direction is the
ordinary connectedness of the canonical fibres of a geometrically connected
morphism.

Arbitrary base-change stability follows from stability of geometric
connectedness and the same equivalence. The final lemma specializes geometric
connectedness to any field-valued fibre. None of these arguments requires
quasi-compactness, finite type, or smoothness.

The module is derived entirely from the existing group-scheme unit and the
published pointed-scheme geometric-connectedness theorem; it supplies the
geometric-connectedness input for the normal multiplicative-type subgroup
argument of SGA 3, Exposé IX, Corollaire 5.5.
