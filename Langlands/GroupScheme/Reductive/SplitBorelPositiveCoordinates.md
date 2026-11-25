# Positive coordinates of contracting points

This is an internal construction derived from the published big-cell coordinate
and dynamic orbit-extension interfaces. Its selected definition is
`Langlands.GroupScheme.LocalSplitCell.positiveCoordinates`.

Fix an arbitrary commutative ring `R`, a finite coordinate torus with a map `i`
to a group scheme `G`, root maps `u` equivariant for characters `ch`, and lists
`neg` and `pos` for which the associated big-cell map is an open immersion.
Let the exponent cocharacter `ν` pair strictly negatively with every character
in `neg`. For every commutative test ring `B`, every map `Spec B → Spec R`,
and every point of the actual dynamic contracting subgroup for `ν`, the module
constructs a unique vector of `pos` coordinates whose ordered root product is
that point. It imposes no localness, reducedness, connectedness or nonzero-ring
hypothesis on `R` or `B` in the arbitrary-ring theorem or coordinate selector.
The positive-character hypothesis is unnecessary for this direction of the
comparison; this module does not prove that arbitrary positive products contract.

`cocharPoint_eq_comp` identifies the existing pointwise coordinate formula with
the actual exponent cocharacter. The local-ring theorem then starts with the
orbit extension supplied by membership in `Dynamic.unipotent`. Its restrictions
are natural in the test scheme, specialize to one at zero, and agree with torus
conjugation at units. Pulling back to the local ring of the line at zero puts
the extension in the open cell. At the generic point of the closed fibre, the
line coordinate becomes a unit, allowing conjugation back into the cell for the
original point. Comparison of cell coordinates, followed by evaluation at zero,
forces the negative coordinates to vanish and the torus coordinate to be one.

The arbitrary-ring theorem applies this local result at every prime of `B`.
It lifts the original point through the open cell, then detects vanishing of
its negative coordinates and triviality of its torus coordinate by localization
at maximal ideals. The empty spectrum case is covered by these same statements.
`positiveCoordinates` selects the resulting vector;
`orderedProduct_positiveCoordinates` proves reconstruction and
`positiveCoordinates_eq` proves uniqueness using the published injectivity of
the ordered positive product.

The proof extends the implemented route of
`LocalSplitCell.exists_orderedProduct_eq_pos` and its arbitrary-ring version,
replacing their explicitly constructed contraction with the orbit extension of
an actual contracting point. Conrad, *Reductive group schemes* (2014),
Theorem 5.1.13, pp.143–145, is the structural motivation: the contracting group
has ordered positive-root coordinates. The present module is the supplied-cell,
supplied-root-map direction of that comparison. It does not construct root
parametrizations, the full scheme isomorphism, or a finite vector-quotient series.
