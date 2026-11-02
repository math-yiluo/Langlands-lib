# Support invariance for actual coactions

This internal helper implements support invariance for the published ring étale equivalence relation and its actual published coaction. The underlying module can have an independent universe and need not be finite.

The symmetry axiom supplies a ring endomorphism reversing the universal arrow of the relation. It exchanges the source and target ring maps. Reversing twice fixes both maps, so the relation's `hom_ext` lemma identifies the square with the identity.

For a coaction θ, define an additive operation on its source tensor module by sending `c ⊗ m` to `reverse(c) • θ(m)`. The existing `coactionCompose` construction ensures that it is balanced over the base ring. This operation is semilinear with respect to arrow reversal. Apply the cocycle identity to the reversed universal arrow and the universal arrow: the composite is the diagonal arrow supplied by the counit. This proves that applying the operation to θ(m) gives `1 ⊗ m`. Semilinearity and involutivity of arrow reversal then prove that the operation squares to the identity on every pure tensor and hence on the tensor module. The construction `reverseTensorEquiv` packages this additive involution.

The annihilator criterion for module support shows that this semilinear involution identifies tensor support with its inverse image under arrow reversal. A support witness x is sent to its reverse; applying the operation to an alleged vanishing scalar multiple transfers the contradiction to the original witness.

The source ring map is flat because it is étale. The flat scalar extension support formula therefore identifies tensor support with the source inverse image of the original module support. Arrow reversal exchanges the source map with the target map, yielding `support_preimage_eq`.

The result uses the actual coaction counit and cocycle laws and the relation's actual symmetry and closed-relation uniqueness. It is a derived implementation by Worker 101 using the published definitions and the pinned Mathlib support APIs. It asserts neither a finite subcoaction nor a nonzero invariant theorem.
