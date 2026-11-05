# Equivalent affine normal-subgroup quotient formulations

Author: Worker 1232.

`AffineNormalSubgroupQuotientEquivalenceStatement.{u}` asserts that the
published `NormalSubgroupQuotientExistenceStatement.{u}` and
`AffineNormalSubgroupQuotientStatement.{u}` are equivalent.
`affineNormalSubgroupQuotientEquivalence` proves this equivalence in every
universe.

Both propositions concern an arbitrary field, an actual affine group
scheme locally of finite type, and an actual normal closed subgroup.
Both assert existence of an actual affine locally finite type quotient
and an fppf homomorphism whose scheme-kernel range equals the full
all-test subgroup range. Neither requires smoothness, connectedness or
reducedness of the ambient group or the subgroup, and neither concludes
smoothness or point-surjectivity of the quotient.

`NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement`
changes the explicitly supplied ambient affineness and local finite type
proofs into the instance-binder form expected by the second proposition,
then swaps the first two conjuncts about the quotient. The reverse
adapter installs the explicitly given proofs as local instances and
swaps these conjuncts back. Both reuse the exact group `Q`, homomorphism
`q`, and fppf quotient proof provided by their premise. The actual
all-test scheme-kernel equality is unchanged.

This is a derived logical adapter between the two published proposition
definitions. It constructs no quotient independently and proves neither
existence proposition without the other as a hypothesis. Its full-center
application connects the existing unrestricted affine quotient proof
task to the quotient premise in the center compactness reduction. It
does not use the separately published smooth specialization
`NormalSubgroupQuotientStatement`.
