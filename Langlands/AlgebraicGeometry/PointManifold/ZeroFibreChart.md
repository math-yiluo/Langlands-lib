# Local coordinates on a zero fibre

This is an internal construction for the algebraic-to-analytic chart proof.
Let `e` be an open partial homeomorphism from an ambient space `E` to a product
`A × B`, and suppose its second component agrees with `F` on its source.
Given one point of the zero fibre of `F`, `zeroFibreChart` restricts `e` to an
open partial homeomorphism from that fibre to `A`. Its source is the preimage
of `e.source`; its target consists of the `y` with `(y, 0)` in `e.target`.
The forward map is the first component of `e` and the inverse, on its target,
is the ambient inverse evaluated at `(y, 0)`.

The inverse uses the given fibre point outside its target to define a total
function. The local inverse identities follow from those of `e`. The source
and target are open by continuous preimage; continuity is inherited by
composition with the subtype inclusion, product inclusion, and projections.
This construction is derived from Mathlib's open partial homeomorphism API;
it asserts no algebraic smoothness or scheme chart existence on its own.

The theorem `zeroFibreChart_contDiffOn_symm_val` proves smoothness of the inverse
followed by inclusion into `E`, at any differentiability order. It assumes that
the ambient map is smooth and has invertible derivative at the zero-fibre
points in its source. At a target point, the ambient inverse lies in the zero
fibre. Mathlib's smooth inverse theorem applies there, and composition with
`y ↦ (y, 0)` gives the result. No invertibility assumption away from the fibre
is needed.
