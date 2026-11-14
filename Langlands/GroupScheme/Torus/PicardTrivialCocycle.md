# Split-torus cocycles over a Picard-trivial affine base

This internal supporting construction applies the unit-coboundary theorem to
each coordinate of a split torus. Let `R` be a commutative ring with trivial
module Picard group, and let `U → Spec R` be affine, flat and surjective. Every
natural cocycle with values in a finite product of copies of the actual
multiplicative group scheme is the coboundary of one torus point on `U`.

`splitPicardCochain` chooses a unit cobounding each coordinate using
`unitCoboundaryOfPicTrivial` and assembles those units through the split-torus
point equivalence. Its `_spec` lemma checks the original cocycle equation on
every test scheme, using naturality of that equivalence and the coordinate
comparison. `isTrivial_split_of_pic_trivial` records the resulting triviality
with the convention `ξ(a,b) = f(a) f(b)⁻¹`.

The coefficient ring may be the zero ring, and no Noetherian or local finite
presentation hypothesis is used. The finite index set can be empty. This
proves vanishing for split tori only; Weil restrictions and other nonsplit
tori require further arguments.
