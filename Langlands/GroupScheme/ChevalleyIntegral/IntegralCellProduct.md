# Ordered products in the integral Chevalley closure

This internal construction multiplies the integral additive root maps and
the full-lattice torus map in the fixed flat schematic closure of a generic
Chevalley group over a Dedekind domain.

`rootProduct` uses the supplied global-section coordinates of a test scheme
as scalar points of the additive group. Its matrix image is the ordered
product of the root exponentials, by induction on the list and the
compatibility of each integral root map. `orderedRootProduct` applies this
construction to the universal coordinates of an ordered root parameter
scheme. Finally, `orderedCellProduct` multiplies the negative root product,
the full-lattice torus and the positive root product. Its matrix composite
is the previously constructed `orderedCellMap`.

The opposite Chevalley data have the same root exponentials and parameter
schemes; only their height functional changes. Thus the same root product
construction handles the negative list. This is derived from the integral
root and torus factorizations and their actual matrix identities.
