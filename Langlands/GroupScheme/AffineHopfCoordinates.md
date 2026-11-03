# Hopf coordinates for actual affine group schemes

Author: Worker 1326.

This internal construction applies Mathlib's equivalence between commutative
Hopf algebras and algebra cogroups to the already published
`AffineCoordinates.coordinateCogroup`. Its comparison with the original group
scheme uses the counit of that equivalence and the published coordinate
comparison; it makes no new external structural assertion.

For an actual affine group scheme `G` over `Spec R`, with `R` any commutative
ring in arbitrary universe `u`, `AffineCoordinates.hopfAlgebra G` is a bundled
commutative `R`-Hopf algebra. Its underlying algebra is precisely the chosen
`AffineCoordinates.algebra G`. The construction
`AffineCoordinates.hopfSpecIso` identifies its relative spectrum with `G` as
an actual group scheme, preserving the group law, identity and inverse.

If the coordinate Hopf algebra is bialgebra-equivalent to a supplied
commutative Hopf algebra `B`, `isoOfBialgEquiv` applies the relative-spectrum
functor to the corresponding Hopf-algebra isomorphism and composes with
`hopfSpecIso`. This gives an actual isomorphism `Spec B ≅ G`, with the
contravariant direction of spectrum explicit.

The group-like elements of this coordinate Hopf algebra form a commutative
group. Its group algebra has the standard commutative Hopf structure. When
`R` is a domain, the coordinate module is torsion-free, and its group-like
elements span it, `groupLikeSpecIso` reconstructs `G` as the relative spectrum
of this group algebra. It uses the proved
`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` and therefore preserves
both the algebra and coalgebra data.

The spanning hypothesis is explicit. This module does not prove spanning after
field-extension descent, does not identify the group-like group with an
integer lattice, and does not conclude splitness for an arbitrary torus or
connected reductivity for an arbitrary dynamic centralizer.
