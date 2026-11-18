# Central additive subgroups of unipotent groups over perfect fields

`Langlands.GroupScheme.perfectFieldCentralAdditiveSubgroup.{u}` proves
`Langlands.GroupScheme.PerfectFieldCentralAdditiveSubgroupStatement.{u}`.
The target is Corollary 14.55, printed p. 297, of J. S. Milne's
*Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`.
See the [statement documentation](CentralAdditiveSubgroupStatement.md)
for the source comparison and the group-scheme conventions.

The Library's perfect-field splitness theorem makes `U` split unipotent.
This is the splitness assertion of Milne, Corollary 16.24, printed p. 331.
[`perfectFieldUnipotentSplit`](PerfectFieldSplitProof.md)

For the trivial action of `U` on itself, the central vector subgroup
theorem gives a closed central subgroup `z : V ⟶ U` with natural vector
coordinates of positive dimension. Here the theorem uses the
nontriviality of `U`.
[`RelativeRoot.splitUnipotentStableVectorSubgroup`](../Rational/SplitUnipotentStableVectorProof.md)

Choose a closed one-dimensional vector subgroup `j : L ⟶ V`. Its vector
coordinates give an isomorphism `e : 𝔾ₐ ≅ L`. The composite
`(e.hom ≫ j) ≫ z` is a closed immersion by composition and is central by
`IsCentral.comp`.
[`VectorFactorPointedFamilies.exists_closed_vectorLine`](../Rational/VectorFactorPointedFamilies.md)
