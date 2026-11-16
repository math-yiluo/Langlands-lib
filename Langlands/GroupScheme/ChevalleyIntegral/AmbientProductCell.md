# Chevalley product parameters in the ambient matrix cell

This internal construction factors ordered positive-root products and the
full-lattice torus through the ambient weight-block subgroup schemes over any
commutative base ring. It derives these maps from the Library's explicit
matrix representation and representability of block subgroup functors.

An ordered product of roots of positive height is block unipotent: its matrix
has diagonal entries one and any nonzero off-diagonal entry has positive
height difference. This follows from `isSUnip_opm`. The universal parameter
point therefore lies in the block unipotent functor. Its representing closed
subgroup supplies `orderedRootToBlock`, whose matrix composite is exactly
`orderedRootMapOver`. For a distinct height-sorted list, closedness of the
matrix map implies closedness of this factor.

The full-lattice torus is diagonal, so it lies in the block Levi subgroup for
the same height weights. Representability gives `torusToBlockLevi` and its
matrix composite. The integral closedness of the torus representation proves
closedness of this factor too.

The negative factor uses the opposite Chevalley data, whose height weights
are the negatives of the original weights. The identity
`inv_comp_diagonalCocharacter_overRing` verifies this sign on the ambient
cocharacter over any ring by evaluating on all test schemes. This extends
the field-scoped identity from `Dynamic.OppositeCellEmbedding`; the proof
uses the same units and diagonal-matrix calculation.

`ambientCellSpace` is the product of the negative block unipotent, block Levi,
and positive block unipotent schemes, associated as the first factor times
the product of the other two. Its multiplication `ambientCellMap` is an open
immersion by the arbitrary-base dynamic triple-cell theorem, applied to the
smooth affine general linear group and the explicit block representatives.

`orderedCellSpace` replaces the two unipotent block factors by their ordered
root parameter spaces and the Levi factor by the full-lattice torus.
`orderedCellToAmbient` is the product of the three factorizations above.
It is a closed immersion whenever each root list is distinct, consists of
roots positive for its respective height, and is weakly sorted by that
height. Stability of closed immersions under products proves the assertion.
Its composite with the ambient cell multiplication is `orderedCellMap`,
the actual product of the negative ordered-root map, torus map, and positive
ordered-root map. Consequently this matrix-valued ordered triple product is
a locally closed immersion.

These results concern the ambient matrix cell. They do not yet identify an
open subscheme of the integral Chevalley closure or prove reductivity.
