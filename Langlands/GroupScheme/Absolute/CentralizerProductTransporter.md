# Centralizer products and their closed inverse-conjugation locus

This internal helper constructs actual multiplication of the images of group scheme maps
`j : M → G` and `b : B → G`. When `j` represents the dynamic centralizer of a cocharacter
`χ` and the full range of `χ` is contained in the range of `b`, every product `m b` conjugates
`χ` into `B`. The assertion holds after every refinement of every test scheme. The proof
uses the published equality of the dynamic centralizer with the all-test torus centralizer:
`(m b)⁻¹ χ(t) (m b) = b⁻¹ χ(t) b`, and the right side belongs to the subgroup range.

Over a field, if `b` is closed, this gives factorization of `productHom j b` through the
actual closed subscheme `ConjugationInto.locus χ b hb`.

`imageClosure j b` is the actual reduced closed subscheme of `G` defined by the vanishing
ideal of the topological closure of the image of `productHom j b`. Its inclusion is closed,
its underlying image is that closure, and it is reduced by the published vanishing-ideal
subscheme theorem. Every closed subscheme through which the product factors also contains
this reduced closure. The proof converts containment of the closure in the closed image
into the inclusion of ideal sheaves required by `IsClosedImmersion.lift`. Thus the closure
also factors through the inverse-conjugation locus and satisfies its all-test predicate.

The closure is connected if the multiplication source is connected, by connectedness of a
continuous image and its closure. In particular smooth connected affine factors over a field
have connected closure: a connected finite-type group scheme is geometrically connected,
and the product is connected by the published geometric connectedness base-change theorem.

All these constructions and deductions use published definitions and results. They do not
assert that the multiplication image is closed or that an intersection is a Borel subgroup.
Those conclusions require further arguments.

`productHom` reuses `SubgroupFunctor.cellMultiplication` for the actual
product map, preserving its arbitrary-base definition and evaluation law.
