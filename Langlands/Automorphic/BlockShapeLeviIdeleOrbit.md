# Finite-dimensional block idele centre orbits on the Levi

`blockLeviScalars` inserts a separate scalar idele in each actual Levi block. Its action `blockLeviScalarAction` on functions is right composition with these block scalars. The scalar matrices commute with all Levi points, so this agrees with left composition for this action.

The restriction of a finite-smooth constant term to the Levi is fixed by principal scalars. For each block, the preimage of the original function's finite level under the finite scalar embedding is an open subgroup that also fixes the restriction. The finite products of these coordinate subgroups still fix the restriction.

The full enveloping-centre orbit on the Levi is finite-dimensional under ambient infinitesimal centre finiteness, contains the restriction, and is preserved by the product of the scalar exponential subgroups. Each block idele is a product of a principal idele, one element of a finite set of representatives, an archimedean sign, an exponential unit, and a member of the open finite subgroup. Because the scalars commute, the factors fixing the original restriction can be applied first. Every translate lies in the sum of the finitely many translates of the enveloping-centre orbit indexed by the representatives and signs. This proves `blockLeviTermRestriction_isFiniteVector` for the actual normalized period used in the proof of `CuspidalSupportExistenceStatement` and supplies the Levi part of the orbit bound preceding Langlands's Lemma 6.

The scalar embeddings used here are defined in [Block constant-term scalar action](BlockConstantTermScalarAction.md).
