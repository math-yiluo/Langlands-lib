# Simple representations of almost-simple groups with finite kernel

`Langlands.GroupScheme.almostSimpleFiniteKernelRepresentation.{u}` proves
`Langlands.GroupScheme.AlmostSimpleFiniteKernelRepresentationStatement.{u}`.
It gives a nonzero simple matrix representation of an almost-simple group
over any field. Finiteness concerns the full scheme-theoretic kernel.

Choose a closed faithful representation and take its finite family of simple
composition factors using `simpleFactorFamily`. If every factor acts trivially,
its nilpotence theorem gives unipotent point matrices in the faithful
representation on all scheme tests.
`IsConnectedReductive.isFinite_of_normal_of_unipotentPointMatrices` then
makes the whole group finite. Pointed maps from a smooth connected affine
group to a finite group scheme are constant.
Applying this to the identity map contradicts noncommutativity. A nontrivial
factor therefore supplies the required nonzero simple representation.

For a nontrivial homomorphism out of the almost-simple group, choose a maximal
torus over the ground field. The kernel on that torus has multiplicative type
and has a largest subtorus with a universal factorization property. Its image
in the ambient group generates a smooth connected closed normal subgroup
contained in the full kernel. Almost-simplicity forces this subgroup to be
trivial, since the homomorphism is nontrivial. Thus the largest subtorus has
trivial inclusion.

Over an algebraic closure, any cocharacter killed by the homomorphism is
conjugate to one in the base change of the chosen maximal torus. That
cocharacter factors through the base change of the kernel on the torus. By
universality it factors through the base change of the trivial largest
subtorus, so it is trivial. The criterion
`kernel_isFinite_of_cocharacter_injective_algClosed` gives finiteness of the
full geometric kernel, and fpqc descent gives finiteness over the original
field.

The source is J. S. Milne, *Algebraic Groups* (2017), Lemma 21.59, printed
p. 442, registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Simplicity is as in Definition 4.15, printed p. 90. The proof selects a
simple subquotient of the faithful representation and derives kernel
finiteness from Definition 19.7 as corrected in
`milne-2017-algebraic-groups-errata-2026-11-02`, entry for printed p. 399,
SHA-256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
The passage through the largest subtorus uses the universal property
proved in `MultiplicativeTypeLargestSubtorusProof`.
