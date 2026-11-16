# Affine neighbourhoods with unit cell coordinates

This internally derived prerequisite combines ring open-cell coordinates with
the affine unit restriction construction. It makes no new external-source
correspondence claim.

`LocalRankOneUnitCell.AffineUnitCellData` records an actual affine open in a
test scheme, an exact lift of a supplied field point, and a factorization of
a supplied group-valued section into negative-root, torus and positive-root
factors with both scalar coordinates units.

`affineUnitCell` constructs these data if the supplied section has a cell
factorization with unit coordinates after pullback to that field point.
The field point lies in the inverse image of the open cell. Choose an affine
open in that inverse image and retain the exact field point by the
open-immersion lifting property. The section factors through the cell there.
Extract its three coordinates and use injectivity of cell multiplication to
identify their pullbacks with the given field coordinates. Both scalar
coordinates are therefore units at the field point. Apply
`affineUnitRestriction` to shrink again, obtaining global units and the
required factorization. All equalities retain the actual scheme morphisms.

No reducedness, noetherianity or locality condition is imposed on the ring.
The field-point factorization remains a supplied input. This module does
not yet apply the construction to the actual relative centralizer or produce
ring Weyl data.
