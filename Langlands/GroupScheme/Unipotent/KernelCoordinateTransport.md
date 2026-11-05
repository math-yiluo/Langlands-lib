# Kernels under coordinate changes

This is an internal categorical construction for actual group schemes. It
supports the coordinate reduction used in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Lemma B.1.7. It is derived
from the universal property of the existing group-scheme kernel, which is a
pullback of the target unit.

`kernelCoordinateIso f g e he` restricts an actual source isomorphism `e`
with `e.hom ≫ f = g` to an actual isomorphism from `kernel g` to `kernel f`.
The forward map and inverse are the induced maps between the two pullbacks,
using `e.hom` and `e.inv` on the source and identity maps on the target and
trivial group. The two inverse laws follow from the pullback projections and
the inverse laws for `e`. The final two formulas record compatibility with
the canonical kernel inclusions.

This construction works over every scheme base. It assumes no coordinate
presentation of an arbitrary group and proves no woundness criterion.
