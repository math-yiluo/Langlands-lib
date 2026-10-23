# Comparison targets for localized tensor unitors and symmetry

This module states the three compatibility equations between the published
symmetric monoidal structure on `X.Modules` and the explicit sheafified
tensor unitors and swap in `Tensor`. All three are proposition definitions
quantifying over arbitrary `X : AlgebraicGeometry.Scheme.{u}` and the
indicated module sheaves. No additional hypothesis is present.

Write `c(M,N)` for the fixed `localizedTensorIso X M N`, directed from
the localized tensor `M ⊗ N` to the explicit `tensorObj M N`. The
monoidal unit is definitionally `structureSheaf X`.

`TensorMonoidalLeftUnitorComparisonStatement` requires that `c(𝒪_X,M)`
followed by the explicit `tensorLeftUnitor M` equals the left unitor of
the localized monoidal category. Both sides go from `𝒪_X ⊗ M` to `M`.

`TensorMonoidalRightUnitorComparisonStatement` requires the analogous
equation for `c(M,𝒪_X)` and `tensorRightUnitor M`. Both sides go from
`M ⊗ 𝒪_X` to `M`.

`TensorMonoidalSymmetryComparisonStatement` requires that `c(M,N)`
followed by the explicit swap `tensorComm M N` equals the localized
braiding followed by `c(N,M)`. Both sides go from the localized `M ⊗ N`
to the explicit `tensorObj N M`.

`TensorMonoidalComparisonStatement` is exactly the conjunction of these
left-unitor, right-unitor, and symmetry equations, in that order and in
the same arbitrary universe.

## Provenance and scope

Worker 59 authored these internal categorical targets. They express
compatibility of the fixed tensor comparison with unitors and braiding,
using the chosen identity identification of the two units. The relevant
categorical conventions are Mathlib's `Functor.LaxMonoidal.left_unitality`
and `right_unitality` in `CategoryTheory.Monoidal.Functor`, and
`Functor.LaxBraided.braided` in `CategoryTheory.Monoidal.Braided.Basic`.
The actual maps and the underlying sheaf construction are already supplied
by the published `Tensor` and `TensorMonoidal` modules. These statements
are not claimed translations of a separate literature theorem.

This module contains no proof of the targets. The localized symmetric
monoidal structure is already constructed; these equations identify its
unitors and symmetry with the previously fixed explicit maps. They do not
assert pullback coherence, tensor-comparison invertibility, a monoidal
pullback instance, or tensor-power arithmetic. Those obligations remain
separate, and a focused proof task must prove this conjunction without
additional assumptions.
