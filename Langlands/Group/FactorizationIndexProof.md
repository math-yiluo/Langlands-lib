# Proof of the compatible factorization index formula

Authors: Worker 103 (original proof and explanation), Worker 1646 (submission and documentation).

The theorem `Langlands.Group.factorizationIndex` proves the exact proposition
`Langlands.Group.FactorizationIndexStatement` at every universe.

Let `q : G → G / N` be the quotient homomorphism. The proof first shows that the
images of `A` and `B` are complementary. Surjectivity follows by lifting an
element of the quotient and factoring its lift in `G`.

For disjointness, suppose `q(a) = q(b)` with `a ∈ A` and `b ∈ B`. Then
`a * b⁻¹ ∈ N`. Factor this element inside `N` into an `A` intersection factor
`c` and a `B` intersection factor `d`. Uniqueness of the original factorization
in `G` identifies `(a, b⁻¹)` with `(c, d)`. Consequently `a ∈ N` and the
common image is the identity. Disjointness of the two image subgroups makes
their multiplication injective.

Mathlib's cardinality formula for complementary subgroups now expresses the
cardinality of `G / N` as the product of the cardinalities of the images.
`Subgroup.relIndex_ker` and `QuotientGroup.ker_mk'` identify the image
cardinalities with the required relative indices. This proof uses natural
cardinalities directly and therefore also respects the infinite-index
zero convention. No compactness or finiteness argument is needed.

This is an internal group-theoretic consequence of the hypotheses in the
published statement, rather than a claim extracted from external literature.
The imported statement and its dependencies are unchanged. The proof is
universe polymorphic and assumes neither finiteness nor topology beyond the
explicit group, normality and compatible factorization premises. It supplies
only the counting step: actual compact open subgroups and rational-point
factorizations must be constructed separately by consumers.
