# Regularity of the actual complementary family

`Langlands.Classification.ComplementaryEndpointRegularity` is an internal,
derived auxiliary target for the endpoint argument of Tadic (1986),
Proposition 2.9, printed p.350. It uses the existing actual smooth
`complementaryProduct`, with independent field and representation universes.
The original complementary-series statement and its hypotheses are unchanged.

For a positive rank and an admissible actual block, the proposition asserts
admissibility of every real complementary product; if the block is also
irreducible, it asserts finite composition length of every such product.
Finally, for any choice of the resulting admissibility proofs, any locally
finite left invariant Borel measure, and any Schwartz--Bruhat test function,
it asserts continuity in the real parameter of the actual finite-rank
distribution character. The trace clause assumes the standard actual general
linear group topology, its Hausdorff, locally compact and nonarchimedean
instances, and its Borel measurable structure, all provided by `T`.

This is a statement only. Its provenance is the specialization of published
Library admissibility, irreducible-product finite-length, and
compact-quotient twisted-induction trace-continuity constructions to the
actual two-block determinant-power family. The latter gives the
character-continuity input used in Tadic's Lemma 2.8 and Proposition 2.9.
This auxiliary statement asserts neither unitarity of the open interval nor
unitarity of any endpoint constituent. Its role is to supply the elementary
regularity inputs to a separate all-constituent character-limit theorem.
