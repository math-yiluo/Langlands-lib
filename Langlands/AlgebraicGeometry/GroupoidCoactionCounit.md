# The counit from extension of the invariant module

Authors: Worker 101, Worker 1203.

For a coaction `θ` on a `B`-module `M`, put
`A = GroupoidCoaction.invariantRing t`. The map `invariantCounit θ` is the
`B`-linear map `B ⊗[A] θ.invariantSubmodule → M` sending `b ⊗ m` to
`b • m`. It is constructed by the heterobasic tensor lifting operation
from the invariant submodule's `A`-linear inclusion into `M`.
The formula on pure tensors is definitional.

`invariantCounit_isHom` proves equivariance between the induced coaction
on its domain and the original coaction on `M`. On a pure tensor, the
semilinearity of `θ` and the invariant equation for `m` give the required
identity. Tensor induction extends it to all elements.
`invariantCounit_natural` checks naturality for an equivariant linear map
by the same pure tensor formula.

The composite of the induced unit with the counit's map on invariants is
the identity: it sends an invariant `m` first to `1 ⊗ m` and then to `m`.
Consequently the counit is always surjective on invariant modules.
If the induced unit on `θ.invariantSubmodule` is surjective, the counit
is also injective on invariant modules: choose unit preimages of two
elements and apply the identity for the composite.

This is internal algebraic infrastructure for the assigned Serre
criterion proof, derived from the unchanged published coaction
definitions and the preceding invariant-module and induced-coaction
constructions. The induced-coaction construction is due to Worker 1203.
The rings lie in `Type u` and the modules in `Type (max u v)`, so the
module universe can be larger and can in particular equal `u`. This
keeps the tensor product and original module in the same universe required
by the published `IsHom` and invariant-map interfaces. These assertions need no
Noetherian, acyclicity, flatness, or ring equivalence relation hypothesis.
They do not yet prove that the underlying counit is bijective or that
an affine quotient exists.
