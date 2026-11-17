# Scalar endomorphisms of highest-weight representations

This derived helper proves the scalar-endomorphism assertion used in
`SplitHighestWeightBaseChangeStatement`. It applies to every finite coordinate
index type and every field in the stated universe.

The construction `MatrixRepresentation.Intertwines.characterSpaceLinearMap`
restricts an actual intertwiner to the corresponding character spaces.
An actual intertwiner carries each character space into the corresponding
character space. The proof checks the character equation at every affine test
algebra, using the intertwining equation and compatibility of matrix-vector
multiplication with scalar extension.

For a highest-weight representation, restrict the endomorphism to the
one-dimensional highest-weight space. Linear algebra makes this restriction
multiplication by a scalar. Subtract that scalar matrix. The difference is an
actual intertwiner, its kernel is stable on all affine tests, and the kernel
contains a nonzero highest-weight vector. Irreducibility makes the kernel the
whole representation, so the original matrix is scalar.

The provenance is the first assertion of Milne, *Algebraic Groups* (2017),
22.4 (printed p. 464), as encoded by the published base-change statement.
The implemented direct invariant-line argument is the route described in that
statement's Markdown, rather than the induced-representation construction in
Exercise 22-1. The character-space preservation lemma is an internal consequence
of the published all-algebra character and intertwiner definitions.

The source is registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The official 2017 errata snapshot (2026-11-02) contains no correction to
22.4. Its change to the induced representation on printed p. 468 is not
used by this direct proof.
