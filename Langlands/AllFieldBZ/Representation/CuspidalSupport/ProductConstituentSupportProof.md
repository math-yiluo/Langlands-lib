# Supercuspidal support of constituents of a normalized product

`Langlands.AllFieldBZ.CuspidalSupport.productConstituentSupport` proves
`ProductConstituentSupportStatement.{uF,uV}`. It applies to every
irreducible subquotient of the actual normalized upper-block product over
an arbitrary nonarchimedean local field. The field universe `uF` and the
universe `uV` of the supercuspidal factors are independent.

A supplied support implies that its factor is irreducible. For each block,
`glSupercuspidalEmbedding` embeds the factor in an ordered normalized
product of supercuspidals. That embedding gives a support because a
subrepresentation is a subquotient. By `glSupercuspidalSupportUniqueness`,
the multiset of the chosen supercuspidal data is the supplied support of
that factor.

`normalizedProduct_embedding_of_factor_embeddings` tensors and induces
the chosen injections. The resulting target is the normalized product of
the blockwise supercuspidal products. The proof flattens the ordered block
refinement and uses `orderedProductRegrouping` to identify that target with
a single normalized supercuspidal product. The flattening equivalence
reindexes the multiset of supercuspidal data as a sum over pairs of an
outer block and an inner block. Grouping that sum by outer block yields
the sum of the supplied supports, with multiplicities.

The regrouping isomorphism gives an embedding of the original product
into the flattened one. `smoothSubquotientTransitivity` makes any given
irreducible subquotient of the original product a subquotient of the
flattened product. Its supercuspidal data therefore witness the claimed
support. For the empty block family, the flattening equivalence has empty
index sets and the multiset sum is empty. Positivity is used only for the
rank of an individual block.

The argument combines exactness and transitivity of normalized induction
with existence and uniqueness of supercuspidal support. See A. V. Zelevinsky,
*Induced representations of reductive p-adic groups II. On irreducible
representations of GL(n)* (1980), §1.1, Proposition (a), (c), printed p. 170,
and §1.10, Proposition, printed p. 174. Section 1.3 on p. 171 identifies the
upper-block parabolic, and §1.8 on p. 174 gives the product notation. The
registered source `zelevinsky-1980-induced-ii` has SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
