# Scalar-extended spans of actual weight spaces

Author: Worker 1317.

Let `k` be a field, `K` a commutative `k`-algebra, `G` an affine group scheme
locally of finite type over `Spec k`, and `i : T.toGrp ⟶ G` a homomorphism from
a commutative group scheme. All these types are in the original universe `u`.

`extendedWeightSpace i χ` is the `K`-linear span, inside the actual Lie kernel
of the scheme pullback `G_K`, of the vectors
`Lie.schemeScalarExtension G (1 ⊗ₜ[k] x)` for `x` in the original actual
all-test-algebra weight space `weightSpace i χ`.

`extendedWeightSpace_le` proves that this span lies in the actual weight space
of the pulled-back character, using the published all-test-algebra comparison
`weightSpace_baseChange_mem` on its generators and closure under scalar spans.

When `K` is nontrivial, `extendedWeightSpace_ne_bot_iff` proves that this span
is nonzero exactly when the original weight space is nonzero. One direction
reduces every generator to zero. In the other, a zero extended span forces
every pure extension of an original weight vector to vanish. Injectivity of
`Lie.schemeScalarExtension` and
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` then force the vector itself to
vanish. A nontrivial algebra over a field is a nontrivial free module and thus
faithfully flat, as supplied by Mathlib's instances.

`iSup_extendedWeightSpace_eq_top` proves that the extended spans cover the
actual pullback Lie kernel whenever the original weight spaces span the
original Lie kernel. Surjectivity of the tensor comparison reduces to tensor
induction. On a pure tensor, submodule-supremum induction expresses its vector
factor using original weight spaces; scalar closure then handles its coefficient.
Tensor addition is handled by linearity.

This is an internal derived construction from `Torus.WeightBaseChange`, tensor
induction, submodule spans and Mathlib's faithfully-flat tensor lemma; it adds
no assertion attributed to external literature. The statements impose no
splitness or reductivity assumption. Equality with the whole pullback weight
space, full support descent, and unconditional relative-root negation remain
separate obligations.
