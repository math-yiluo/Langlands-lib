# Scalar transitions on vector groups

This internal supporting construction defines multiplication by a scalar on the
actual polynomial vector group over any commutative ring. Its coordinates are
specified on every scheme test. The scalar maps compose by multiplication and
unit scalars induce group-scheme isomorphisms. The coefficient map on each
test scheme is the existing `Langlands.GroupScheme.scalarMap` from
[Reductive/Basic](Reductive/Basic.md).

The all-test pullback coordinates identify base change of the polynomial vector
group with the polynomial vector group over the new ring. This identification
commutes with the scalar map through the given coefficient homomorphism.

Over a field, the actual pullback kernel of a scalar map is smooth, connected
and unipotent. A zero scalar has the full vector group as kernel, with an
explicit group-scheme isomorphism. A nonzero scalar is a unit and gives the
trivial kernel. Smoothness and connectedness are transported through these
isomorphisms. Unipotence uses the published all-coefficient representation
theorems for the vector group and the trivial group. The same conclusion holds
after any ring-to-field specialization, by the commuting base-change square.

This calculation is an internal geometric input for the additive and trace-zero
transition calculations of Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Facts C.2.1 and C.3.1, printed p.698 / PDF p.729, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. It does not construct the
root-filtration models, restriction-of-scalars comparisons, or their
identification with a supplied apartment filtration.
