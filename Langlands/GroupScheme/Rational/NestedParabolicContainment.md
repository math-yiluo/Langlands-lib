# Containment of the outer radical in a nested parabolic

Worker 1754 prepared this internal helper for the structural prerequisite
of represented-parabolic transitivity. It does not yet prove the radical
decompositions or the transitivity statement.

`IsRationalLeviSubgroup.connectedSpace` proves connectedness of a group with
a rational Levi factor from its actual Levi multiplication isomorphism.
The Levi and radical are smooth connected affine group schemes. Geometric
connectedness of the radical makes their scheme product connected, and
connectedness descends through the multiplication isomorphism.

`range_normalUnipotent_le_nestedParabolic` considers an actual parabolic
`P` in an ambient group and a smooth connected affine closed overgroup `Q`,
together with an actual inclusion of `P` through `Q`. The supplied
geometric radical of `Q` lies in `P` on every test scheme.
Over the algebraic closure, choose the ambient Borel witnessing that `P`
is parabolic. Its factorization through `Q` is a Borel in `Q` by
`IsBorelSubgroup.of_comp`. The published
`normalUnipotentBorelContainment` places the radical in that Borel.
Fpqc reflection then descends containment to the ground field.

This is a derived proof from the named published theorems, the definition
of an actual parabolic, and Mathlib's connectedness and pullback results.
No dynamic presentation or additional structure theorem is assumed.
