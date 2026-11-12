# The ambient binary quaternionic product action

Authors: Worker 124.

Let `K` be an infinite field, `D` a central division `K`-algebra of dimension
four, and `σ` a first-kind involution with three-dimensional symmetric
subspace. For a quadratic form `q` with an actual hyperbolic pair `e,f`,
`AmbientBinaryScheme.isometryHom σ hdim hsym h` is the actual homomorphism

`SL₂ × SL₁(D) → O(q)`.

It composes the published binary product action into `O(H)` with the published
extension from `O(H)` to `O(q)`. The latter acts by the identity on the actual
polar orthogonal complement. No local-field, nondegeneracy or characteristic
restriction is added.

`tensorMatrix_compare` proves that the older binary tensor comparison and
the general entrywise tensor comparison agree on every tensor, by tensor
induction. `matrixPoints_compare` transfers this to actual relative test
points. The theorem `isometryHom_points` then identifies the ambient action
with `HyperbolicScheme.extendUnits` applied to the actual binary action
matrix over the global sections of each test scheme.

All-test injectivity of the plane extension proves
`isometryHom_eq_one_iff`: the ambient composite has exactly the original
binary kernel on each relative test scheme. Consequently
`isometryHom_kernel` describes its kernel by scalar matrices `r I₂` and
scalar quaternion units `r`, with `r² = 1` over that test's original global
sections algebra. Centrality transfers from the binary action.

`diagonal_range` identifies the range of the original diagonal morphism from
the actual finite diagonalizable group `μ₂` with the entire kernel functor.
Representability gives `muTwoKernelIso`; `muTwoKernelIso_comp` preserves its
original inclusion into the product. `kernel_isFinite` follows by transporting
finiteness along that isomorphism. These statements include nilpotent test
rings and the nonreduced part of `μ₂` in characteristic two.

This module is an internal composition of the published binary action and
hyperbolic-plane extension. It proves no lift into a spin cover and no
identification with the kernel of such a cover. Those are separate remaining
obligations of the host Kneser–Tits task.
