# Real twists of actual refined Jacquet modules

Author: Worker 99.

This is an internal specialization of published quotient constructions, for the
persistence of cuspidal exponents. It introduces no geometric-lemma assumption.
The field universe and the two representation-carrier universes are independent.
Every rank, block shape, actual refinement and real coarse parameter is allowed;
the representations need not be irreducible, admissible or smooth.

The existing `normalizedRefinedJacquetRealTwistEquiv` from
[RefinedJacquetRealTwist](../Geometric/RefinedJacquetRealTwist.md) identifies the actual normalized refined
Jacquet quotient of `T.leviRealPowerTwist B t ρ` with the twist of the normalized
refined Jacquet quotient of `ρ` by the restriction of the coarse character to
the common refined Levi. Both quotients use the same supplied full modulus
`T.refinedLeviModulus B S`. The equivalence and its inverse send the quotient
class of each vector to the class of that same vector. The naturality theorem
added here states the corresponding equality of intertwining maps for every ambient
intertwiner, without an injectivity or surjectivity condition.

This module reuses that equivalence with its argument order `B S ρ t` and
specializes `Jacquet.normalizedActionOfModulusTwistEquiv_naturality`. Its
kernel premise is the already proved
`T.refinedUnipotent_le_ker_leviRealPowerCharacter`: the determinants of elements
of each actual refined unipotent radical are one. Thus the character does not
change the radical action or its relation submodule.

`leviRealPowerCharacter_refinedLevi` derives the restriction formula from the
published `Langlands.refinedLeviRealTwist` theorem by evaluating its character
clause on the actual refined Levi section. The theorem is instantiated with
the trivial representation only to select its universally quantified character
clause. In flattened coordinates the existing `leviRealPowerCharacter_flatten`
from [MaximalConeLifting](../Classification/MaximalConeLifting.md) supplies the
same pointwise identity: the fine parameter repeats each coarse entry in all
its refined blocks.
`flattenedNormalizedRefinedJacquetRealTwistEquiv` uses this character identity
and the same linear equivalence to express the quotient comparison on the
actual flattened product Levi. It retains both quotient representative formulas.

These are actual representation equivalences and equations of maps. They do
not assert occurrence of a constituent, location in a geometric piece,
cuspidal-support identification or persistence at the untwisted parameter.
Those conclusions require separate arguments.
