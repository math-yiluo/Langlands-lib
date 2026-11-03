# Open cells in subgroup quotients

This internal module derives an open immersion into an actual scheme quotient
from an open multiplication cell. It works over any base scheme. The group
schemes, maps, fiber criterion and geometric properties of the projection are
explicit hypotheses; their construction for dynamic parabolics remains a
separate obligation.

For a group homomorphism `i : H → G`, a relative scheme map `j : X → G` and
an actual quotient map `q : G → Q`, the morphism `multiplication i j` sends
`(x,h)` to `j(x)i(h)`. Suppose `i` is a monomorphism and equality after `q`
is exactly right-coset equivalence on every test scheme.
`multiplication_isPullback` proves that the square with top edge
`multiplication i j`, left edge the projection to `X`, right edge `q`, and
bottom edge `j ≫ q` is cartesian.

The proof factors `j(x)⁻¹g` through `i` whenever `j(x)` and `g` have the
same quotient image. This gives a lift to `X × H`. Group cancellation and
the monomorphism `i` give uniqueness on every test scheme.
If `q` is surjective, flat and quasi-compact and multiplication is an open
immersion, Mathlib's fpqc descent of open immersions then implies that
`j ≫ q` is an open immersion.

Over a commutative coefficient ring, `sectionOverImage` inverts the
isomorphism from the cell to the open image of `j ≫ q` and then composes
with `j`. `sectionOverImage_comp` verifies that its composite with `q` is
the existing `openOverι` inclusion. `range_subset_image` proves containment
of the entire underlying range of every rational point coming from the
cell. `exists_localSection` assembles the actual open, section and both
properties. Applied to the opposite unipotent cell, this supplies the
identity-coset section once the cell and quotient hypotheses have been proved.

Provenance: elementary group laws, the universal property of a categorical
pullback, and the pinned Mathlib descent theorem. This is the formal
geometric bridge used by the opposite-cell construction of local sections.
It proves no quotient existence or properness assertion and no rational-point
lifting theorem.

Author: Worker 424.
