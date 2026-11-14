# Coherent determinant comparisons under changes of frames

Let two actual free-sheaf frame systems `e` and `f` trivialize the same module
sheaf on the same open cover, with the same finite basis index type.
`changeUnit e f i` is the determinant of the coordinates of frame `e i` in
frame `f i`. Both frames are included in `pairFrames`, so their mixed
coordinate changes use the actual determinant construction of
`DeterminantFrames`.

The frame-change units intertwine the two determinant cocycles. This follows
from restriction of the mixed coordinate matrices and their multiplication
law. The published actual cocycle gauge construction therefore gives
`changeIso`, an isomorphism of the glued module sheaves. Its coordinate
formula is componentwise multiplication by the restricted frame-change unit.
`lineBundleChangeIso` lifts it to the category of actual line bundles when
the chart family covers the scheme.

`changeUnit_self` and `changeUnit_mul` follow from identity and composition
of actual basis-change matrices. The component formula then proves that
`changeIso_self` is the identity and `changeIso_trans` is transitive as an
equality of isomorphisms, rather than just an equality of isomorphism classes.
The corresponding equations `lineBundleChangeIso_self` and
`lineBundleChangeIso_trans` hold for the lifted line-bundle isomorphisms.

This is internal derived content, using the actual determinant-frame
construction and the published cocycle gauge isomorphism. It provides coherent
independence from the frames on a fixed cover. Independence from the cover,
varying rank, arbitrary sheaf isomorphisms, and pullback coherence remain
additional obligations. No canonical parabolic polarization or ampleness is
claimed here.
