# Stabilizer-fixed character lines in original irreducible representations

This is an internal prerequisite for the fixed-field endomorphism statement in
the classification of representations of groups of multiplicative type by
Galois orbits of characters.

For an original representation over `k` and a Galois field extension `K/k`,
`orbitLineSubspace v` is the sum of the coefficientwise Galois conjugates of the
line through `v`. If `v` is a character vector, this sum is stable on every
affine algebra test and is invariant under coefficientwise Galois conjugation.
The actual subspace descent theorem and original irreducibility imply that the
sum is the entire extended coordinate space when `v` is nonzero.

Let `H` be the stabilizer of a nonzero geometric weight `χ`. The character space
is `H`-invariant by the actual Galois compatibility theorem.
`SubgroupFixedVectors.exists_fixed_pi` produces a vector `v` in this space fixed
by `H`, with one coordinate equal to one. The character projector for `χ` sends
every conjugate of `v` either to zero, or to `v` itself: in the latter case the
conjugating automorphism is in `H`. Since the conjugate lines span, the whole
`χ`-space is the line spanned by `v`.

The conclusion does not require a multiplicative-type hypothesis: it holds for
any original irreducible actual representation admitting a geometric character
vector after a Galois extension. No finite-degree or finite-stabilizer hypothesis
is used. It is the multiplicity-one step of the coordinate route to Milne,
*Algebraic Groups* (2017), Theorem 12.30, printed pages 241–242, registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The implementation uses minimum support and character projections in place of
an appeal to a finite stabilizer's semilinear descent equivalence.
