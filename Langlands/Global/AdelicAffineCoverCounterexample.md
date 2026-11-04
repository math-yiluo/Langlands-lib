# An actual binary affine-line cover and explicit adelic points

The generic definitions use the actual affine line
`ringTest R (MvPolynomial Unit R)` over a commutative ring `R`.
`affineLineBinaryOpen R false` is the basic open D(t), already constructed
as `affineLinePuncturedOpen`; the `true` branch is the actual basic open
D(1-t). `affineLineBinaryPointUnion` is the union of the images of actual
relative scheme morphisms into these open subschemes under their open
inclusions. `affineLineTopPointUnion` is the image for the singleton open
cover consisting of the whole affine line. These are subsets of actual
`RingPoint` spaces; no topology or cover-surjectivity assumption is supplied.

For a number field `K`, `numberFieldAffineCoverCoordinate` is the actual
full adele `(0,1)`: zero at every infinite place and one at every finite
place. `numberFieldAffineCoverPoint` is its actual relative affine-line
point, constructed by the inverse of the published coordinate equivalence.
All infinite completions remain in the value ring.

For a function field `F` over `k`, `curvePlaceAffineCoverCoordinate` is zero
at `curvePlaceReference k F`, the chosen actual discrete place extending
the rational-function place t=0, and one at every other actual place.
Every coordinate lies in the actual completed valuation subring; the
restricted-product membership proof uses this at every place, rather than
assuming a restricted-product presentation. The coordinate itself is
constructed over any constant field with the specified original scalar
tower and finite extension of `RatFunc k`. With finite `k`, the existing
full-field diagonal gives the original `F`-algebra action on the actual
adele ring. `curvePlaceAffineCoverPoint` is the resulting actual relative
affine-line point. There is no separability assumption on the function field.

This is a derived concrete realization of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.9,
Example 4.1. The source asserts that affine-open point images need not cover
adelic points and their union can depend on the affine cover, without
specifying this binary affine-line example. The cover proof, the
unit-coordinate descriptions of its point images, the existence of the
needed distinct places and failure of coverage for these explicit points
are separate statement and proof obligations. This definition unit alone
does not claim them proved.

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
