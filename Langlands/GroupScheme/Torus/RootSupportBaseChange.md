# Actual roots of a split torus after field extension

Worker 416. Let `G` be an affine group scheme locally of finite type over a
field `k`, and let `i : T → G` be a homomorphism from a split commutative
torus. For every extension field `K/k`, this module proves that the actual
root set of the pulled-back homomorphism is exactly the image of the original
root set under the canonical character pullback. The universe `u` is arbitrary.
Neither reductivity nor maximality of the torus is required.

The proof uses the published decomposition of the actual Lie kernel as an
internal direct sum of all character weight spaces. The published scalar
extension equivalence identifies the extended Lie kernel with the Lie kernel
of the actual scheme pullback, and carries every pure weight vector into the
weight space of the pulled-back character. The tensor-support lemma in
`Langlands.LinearAlgebra.InternalTensorSupport` therefore proves
`weightSpace_baseChange_eq_bot_iff`.

The canonical character pullback for a split torus is an additive equivalence.
It preserves and reflects zero characters. A root is precisely a nonzero
character with a nonzero weight space, so the preceding equivalence of zero
weight spaces proves `mem_roots_baseChange_iff`. Surjectivity on characters
then proves the set equality `roots_baseChange`.

`rootsBaseChangeEquiv` restricts the canonical character equivalence to the
actual root sets; its forward map is actual pullback on characters.

This is an internal consequence of the published Lie scalar extension,
all-test-algebra weight decomposition, and split-lattice pullback results.
It requires no assumption about separability, perfection, algebraicity or
finiteness of the field extension. It does not assert root-datum existence,
normalizer transport, or simple connectedness.

The local affineness and finite-type instances for the base-changed group
have explicit module-specific names, so the related torus comparison modules
can be imported together without generated-name collisions.
