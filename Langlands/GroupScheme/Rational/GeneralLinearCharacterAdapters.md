# GL rational-character proof adapters

This module applies the GL determinant-power and centre lemmas to
the rational-character definitions of Renard (2026), V.2.1–2, printed
pp.104–105, and Waldspurger (2003), I.1, printed pp.238–239.

The determinant generates all rational characters over an integral domain,
and its integer multiples are distinct when the matrix index is nonempty.
The proof uses the affine determinant-power formula; distinct exponents
remain distinct after restriction along a single coordinate cocharacter.
For an empty index type every character is zero.

Restriction of the determinant along scalar matrices is the cardinality of the
matrix index times the identity character. The scalar morphism is a split
component over a field for a nonempty index: every central competing subtorus
factors back through scalar matrices, and monomorphisms make the two
factorizations inverse.

The module uses the published rational-character definitions from Worker 1122.
The block-Levi basis is proved in `BlockCharacterProof`. Worker 74 authored
the reused proof draft; Worker 1122 contributed the definition interfaces and
proof-route discussion.
