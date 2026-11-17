# Reduction of finite-subgroup spreading to a uniform exponent

The entry construction
`Langlands.GroupScheme.FiniteSubgroupSpreadingReduction.spreadingNeighbourhoods_of_uniformExponent`
returns two operations on the given subgroup and base point. From a finite
residue fibre, the first chooses an actual open neighbourhood, a positive
integer, its all-test-point power identity, and finiteness. This data is
packaged as `FiniteNeighbourhood K s`. From a trivial residue fibre, the
second chooses a `FiniteUnitFibreSpreading.TrivialNeighbourhood K s`,
including the actual structure isomorphism. The first operation is also
available as `finiteNeighbourhood_of_uniformExponent`.

The theorem
`Langlands.GroupScheme.FiniteSubgroupSpreadingReduction.finiteSubgroupSpreading_of_uniformExponent`
proves the implication

```text
QuasiFiniteCommutativeUniformExponentStatement.{u} →
MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u}.
```

The consequent is the unchanged published target declaration, imported
from its original module. The theorem works in every universe `u`.
Its sole mathematical premise is the uniform-exponent proposition.
It adds no hypothesis to the schemes, groups, subgroup, or base point
quantified by the target. In particular, it adds no flatness assumption.
This contribution does not prove the premise, so it does not supply an
unconditional proof of the spreading target.

The supporting modules contain the actual subgroup finiteness,
local quasi-finiteness, relative geometry, and finite-group
trivial-fibre constructions. The proof assembles them as follows.

First the relative multiplicative-type geometry gives an affine
commutative source for any closed subgroup `i : K ⟶ H` of the
specified multiplicative-type group. Local finite presentation in
the target gives local finite type. The finite residue-field fibre
therefore supplies an open neighbourhood `Q` on which the subgroup
is locally quasi-finite, by
`FiniteFibreQuasiFiniteNeighbourhood.exists_locallyQuasiFinite_neighbourhood_of_isFinite_fibre`.

Choose an affine open neighbourhood `U` of the base point inside `Q`.
Its underlying space is quasi-compact. The structure morphism of
the actual base-changed subgroup `K_U` retains local finite
presentation, quasi-compactness, and quasi-separatedness.
Commutativity is preserved by base change. The standard comparison
between repeated base change and base change along a composite
transports local quasi-finiteness from `K_Q` to `K_U`.

The supplied uniform-exponent proposition now gives one integer
`n > 0` killing every point of `K_U` on every `U`-scheme.
The base change of `H` is still of multiplicative type, and the
base-changed inclusion is still a closed subgroup. Applying
`RelativeMultiplicativeType.IsMultiplicativeType.isFinite_closedSubgroup_of_uniformPower`
gives finiteness of `K_U`. This proves the full 6.4 clause,
including both the all-test-point power identity and finiteness.
The first intermediate theorem
`finite_neighbourhood_of_uniformExponent` records this clause.

For the 6.5 clause, an isomorphic residue-field fibre is finite.
The first intermediate theorem yields a finite neighbourhood.
`FiniteUnitFibreSpreading.exists_isIso_neighbourhood_of_finite_neighbourhood`
then supplies a smaller open neighbourhood on which the structure
morphism is an isomorphism. The theorem
`unit_neighbourhood_of_uniformExponent` records this clause.
The final theorem forgets the chosen neighbourhood data to its existence
claims, with exactly the quantifiers and hypotheses of the imported target.

This is derived internal content: it composes the precise supporting
constructions with the explicitly supplied uniform-exponent
proposition. The route implements the division of SGA 3, Exposé IX,
Lemmas 6.1 and 6.3, Theorem 6.4, and Corollary 6.5. Those source
statements are not strengthened here. The remaining uniform-exponent
proof is a separate obligation.

Worker 877 assembled the reduction, the bounded-exponent finiteness
argument and the finite-group trivial-fibre argument. Worker 887
supplied the local quasi-finiteness and arbitrary-base relative
geometry constructions.
