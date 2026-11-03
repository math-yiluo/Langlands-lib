# Actual adjoint weight vectors under scheme base change

Author: Worker 1317.

This is an internal consequence of the actual Lie-kernel scalar-extension and
scheme-pullback comparisons. It constructs the tensor equivalence for the
base-changed group scheme and proves the forward comparison for actual adjoint
weight vectors. No reductive-group structure theorem is used.

For commutative rings `k` and `K`, a `k`-algebra structure on `K`, and a compatible
`K`-algebra `A`, `Lie.affineBaseChangeEquiv_target` states that the affine-point
pullback comparison commutes with group homomorphisms. It follows by composing
the published pullback-adjunction comparison with the identity isomorphism of
the affine test schemes, then using associativity.

`Lie.characterValue_baseChange` states that a base-changed character has the
same unit value as the original character on the corresponding original
`A`-point. The proof uses naturality of the multiplicative-group point
identification, its canonical scheme base-change isomorphism, and the identity
map underlying the affine test-scheme comparison.

Now let `k` be any field, `K` any commutative `k`-algebra, and `G` an affine
locally finite-type group scheme over `Spec k`, all in the original universe.
Write `G_K` for its actual scheme pullback to `Spec K`.
`Lie.schemeScalarExtension` constructs the `K`-linear equivalence

`K tensor_k Additive(lieKernel G k) ≃ Additive(lieKernel G_K K)`.

It is the composite of `Lie.kernelScalarExtension` with the inverse of the
actual scheme-pullback Lie comparison. Its pure-tensor formula sends
`c tensor x` to `c` times the inverse pullback comparison of the coefficient
image of `x`. `Lie.schemeScalarExtension_base_naturality` proves that the image
of `1 tensor x`, mapped to every compatible `K`-test algebra and then compared
with the original group, is exactly the direct coefficient image of `x`.
This uses coefficient naturality of the pullback comparison and the successive
coefficient-map identity for base Lie vectors.

Finally, for every commutative group scheme `T`, homomorphism `i : T.toGrp -> G`,
character `chi`, and `x` in the actual weight space `weightSpace i chi`,
`weightSpace_baseChange_mem` proves that the image of `1 tensor x` belongs to
the weight space of the base-changed inclusion and character. For every
`K`-test algebra the proof installs the induced compatible `k`-algebra
structure, applies injectivity of the actual pullback Lie comparison, and
reduces the defining weight equation to the original one. Adjoint compatibility
is used at every test-algebra point, together with the character-value and
coefficient identities above. Neither `T` nor `K` is assumed split, smooth,
reductive, or nontrivial.

This contribution gives a forward vector comparison. It does not yet identify
whole weight spaces, prove nonvanishing after field extension, descend weight
support, or prove unconditional relative-root negation.
