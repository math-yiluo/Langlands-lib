# Restricting a coaction to the actual quotient rings

Let `B` and `C` be commutative rings in an arbitrary universe `u`, let
`s : B →+* C` be the given algebra map, let `t : B →+* C` be the target,
and let `M : Type v` be a `B`-module carrying the unchanged published
`GroupoidCoaction t M`. For an ideal `I` satisfying
`I.map s = I.map t`, this module constructs `idealRestriction θ I hI`,
a coaction on `M/IM` for the actual target quotient map
`quotientTarget I hI : B/I →+* C/s(I)`. The source algebra on these
quotient rings is Mathlib's canonical quotient algebra. The module
universe `v` is independent of the ring universe `u`.

The tensor comparison used in this construction is injective without
flatness assumptions. First, `rTensor_quotient_injective_of_annihilator`
considers any ideal `J` of `C` annihilating `C ⊗[B] N`. Tensor right
exactness identifies the kernel of the tensor of `C → C/J` with the
image of the tensor of its kernel inclusion. This inclusion induces the
zero map: if `c` belongs to the kernel, its action on `1 ⊗ n` is zero,
and that action is `c ⊗ n`. Tensor induction therefore gives a zero
image and injectivity.

For `N = M/IM`, the previously proved
`map_source_le_annihilator_tensor_quotient` supplies this annihilation
for `J = I.map s`. The lemma `quotientModule_scalarTower` installs the
compatible `B → B/I → N` actions using the torsion property of `M/IM`.
To change the tensor base from `B` to `B/I`, every scalar in `B/I` is
lifted to `B`, where the tensor balancing identity applies. Mathlib's
`equivOfCompatibleSMul` then identifies
`(C/s(I)) ⊗[B] N` with `(C/s(I)) ⊗[B/I] N`. Tensor induction identifies
the composite of this equivalence and the injective coefficient
quotient map with `scalarChangeTensor`. This proves
`idealRestriction_tensor_injective`.

The definition `idealRestriction` applies the generic `scalarChange`
construction to `idealQuotient θ I hI.ge`. Surjectivity of `B → B/I`
and the formula for `quotientTarget` provide its compatibility inputs.
Thus its counit and cocycle are those already proved by scalar change
for the full published coaction structure. Finally,
`idealRestriction_mem_invariants_iff` applies tensor injectivity to
reflect the actual unit-tensor equation: an element of `M/IM` is
invariant for the restricted coaction if and only if it is invariant
for `idealQuotient θ I hI.ge`.

This is an internal derivation from the existing quotient and scalar
change helpers, tensor right exactness, and compatible scalar actions.
It introduces no literature assertion and assumes no affine quotient
or descent conclusion. No étale relation, Noetherian, finite-generation,
Artinian, or acyclicity hypothesis is needed here. The helper does not
assert existence of a nonzero invariant or the full Serre criterion.
