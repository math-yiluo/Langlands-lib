# Subgroup lemmas for compact inheritance by a Levi

These internal group and topology lemmas support the proof of the published
`StandardLeviCompactInheritanceStatement`. They restrict an injective and surjective
ordered intersection product to a subgroup when all three factors remain in it.
Nested radical products and a trivial opposite-radical/parabolic intersection
supply that factor condition. For a semidirect parabolic decomposition they also
construct the image of a subgroup intersected with the parabolic, prove compactness
under a continuous projection and closed parabolic, and prove the inherited
containment and normalization when projection preserves the specified level.

The arguments are derived elementary subgroup calculations for the proof of
Renard VI.10.6; these helper claims are not separately attributed to the book.


The proof of `restrict_iwahori` sends triples in the restricted subgroup to the
original product. Its injectivity follows from the original injectivity, and its
surjectivity uses the explicit hypothesis that all factors of a product in the
restricting subgroup belong to that subgroup. `factors_mem_of_nested_radicals`
writes the opposite factor as `a*b` with `a` in the larger opposite radical and
`b` in the Levi. The product condition puts `a` in the parabolic, hence `a=1`.
The remaining factors then belong to the Levi by subgroup arithmetic.

`projectedSubgroup` is the image of `K₀.comap P.subtype` under the composite of
the semidirect projection with the Levi inclusion. It lies in the Levi by
construction. The projection is the identity on the Levi, giving containment
of `K ∩ M`. For normalization, conjugate a level element by an element of
`K₀ ∩ P`, use the assumed normalization in the ambient group, and apply the
projection homomorphism. Its level-preserving hypothesis places the resulting
conjugate in `K ∩ M`. Compactness follows because the inclusion of a closed
parabolic is a closed embedding: its inverse image of the compact subgroup is
compact, and its continuous projected image is compact.
