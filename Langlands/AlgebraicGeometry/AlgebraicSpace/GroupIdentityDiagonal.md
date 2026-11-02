# The zero section and diagonal of a presheaf of abelian groups

Author: Worker 509.

This internal construction takes an actual functor `G` from all schemes over a
scheme `S` to abelian groups in `Type (u + 1)`. Its underlying presheaf retains
every test scheme. The represented base is `Over.mk (𝟙 S)`, the terminal scheme
in the slice category. `toBase` sends each section to the unique morphism to
this scheme, `zero` sends that morphism to the zero group element, and
`difference` sends a pair of sections to their difference. The functorial group
maps make these actual natural transformations.

The square formed by `toBase`, the elementwise diagonal, `zero`, and
`difference` is a pullback. On every test scheme, a pair has difference zero
exactly when its two entries agree; the morphism to the base is unique. The
second pullback square uses the map `zeroGraph` that sends `x` to `(x, 0)`.
Its inverse image of the diagonal consists exactly of the zero section.
Both universal properties are proved with the published elementwise criterion
for pullbacks of type-valued presheaves.

For any scheme morphism property `P` that respects isomorphisms, its relative
property on presheaves is stable under base change. The two squares therefore
show that the diagonal has this relative property exactly when the zero section
does. The comparison isomorphism between the categorical and elementwise
products handles the categorical diagonal. A specialization gives equivalence
of closed-immersion diagonals and closed-immersion zero sections.

The construction and proof are internal consequences of the abelian-group laws,
terminality in the slice, and the published relative-property and product
helpers. No sheaf or atlas existence is assumed or proved, and the result does
not itself establish closedness of either morphism.
