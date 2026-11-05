# Local trivializations of split-torus cocycles

Author: Worker 1232.

For a scheme `S` in an arbitrary universe, a finite index type `I` in that
universe, and a cover `U → S`, this module constructs local trivializations of
cocycles valued in the actual group scheme `splitTorus S I`. The cover is assumed
affine, flat and surjective; neither the base scheme nor the cover scheme is
required to be affine.

`Cocycle.LocalTrivialization ξ y` records an actual open neighbourhood `W` of a
base point `y`, a torus point `f` on the inverse-image open of the cover, and the
identity `ξ(a,b) = f(a) f(b)⁻¹` on every over-test scheme mapping into that open.
The restricted cover and its group points remain over `S`, so this structure
does not assert a global trivialization.

The construction is derived from the existing unit-cocycle descent theorem and
the natural multiplicative point model of the split torus. First
`Cocycle.unitCoordinate` converts each coordinate to a unit cocycle on arbitrary
scheme maps with the same composite to `S`. `unitCoordinate_eq` compares this
with the original over-category formulation, including different presentations
of the same structural map. Naturality and the cocycle identity follow from
those of `ξ`.

`finiteLocalFrame` supplies one common neighbourhood and a unit section in each
coordinate. `frameUnit` reads those sections as global units of the restricted
cover; `frameUnit_pullback` checks the comparison with direct pullback from the
original cover. The frame law is `ξ_i(a,b) σ_i(a) = σ_i(b)`.
`frameCochain` therefore uses the inverse units as its coordinates.
`frameCochain_spec` proves the required coboundary identity by the split-torus
point equivalence and commutativity of units. `localTrivialization` packages
this construction at any base point, also allowing an empty coordinate type.

No external structural theorem is introduced here. Transport to an arbitrary
split torus, descent of a corrected point to a section of a represented quotient,
and the compactness of the full centre point quotient are separate obligations.
