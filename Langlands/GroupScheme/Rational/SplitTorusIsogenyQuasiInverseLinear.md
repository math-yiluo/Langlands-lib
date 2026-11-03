# An integer quasiinverse from a finite cokernel

Author: Worker 1444.

This internal supporting module constructs an integer-linear reverse map for an
injective integer-linear map with finite cokernel. It applies in particular to
maps between finite function lattices, but does not require finite generation
or freeness of either module.

## Construction and identities

Let `M` and `N` be additive commutative groups, equipped with their canonical
integer module structures, and let `f : M →ₗ[ℤ] N` be injective. Assume that the
actual quotient `Q = N ⧸ LinearMap.range f` is finite. Its order `n = Nat.card Q`,
regarded as an integer, is nonzero because `Q` contains zero.
All declarations below are in `Langlands.GroupScheme.SplitTorusIsogeny`.

`cokernelCard_smul_mem_range` shows that `n • y` lies in `f.range` for every
`y : N`: its quotient class is `n` times the class of `y`, which is zero by
Mathlib's finite-group order theorem `card_nsmul_eq_zero'`. This preliminary
lemma also holds when the quotient is infinite, because `Nat.card` is then
zero.

`quasiInverseOfFiniteCokernel` first restricts the codomain of `n • id` to
`f.range`, using this membership lemma. It then composes with the inverse of
the linear equivalence `LinearEquiv.ofInjective f hf : M ≃ₗ[ℤ] f.range`.
Thus the construction is an actual integer-linear map `g : N →ₗ[ℤ] M`;
it is not merely a choice of preimages without a proof of linearity.

`comp_quasiInverseOfFiniteCokernel` proves `f ∘ₗ g = n • id` using the inverse
identity of that equivalence. `quasiInverseOfFiniteCokernel_comp` proves
`g ∘ₗ f = n • id` by applying the injective map `f` and using the first
identity and integer-linearity.

`exists_quasiInverse_of_injective_finiteCokernel` packages the construction
and its two identities with the nonzero integer `n`. It accepts the finiteness
of the actual cokernel as an explicit proof argument. Its source and target
groups may lie in independent universes. Empty coordinate index types are
allowed when this is specialized to function lattices.

## Provenance and scope

These are internal deductions from the elementary finite-group order identity,
the quotient module, and the equivalence of an injective linear map with its
range. No external geometric theorem is asserted. The module does not derive
injectivity or finite cokernel from an isogeny, nor does it realize the reverse
linear map as a group-scheme homomorphism. Those remain inputs to the geometric
part of the split-torus isogeny cocharacter proof.
