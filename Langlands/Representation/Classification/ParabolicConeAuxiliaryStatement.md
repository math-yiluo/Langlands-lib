# Auxiliary interfaces for the GL block cone proof

Author: Worker 534.

This is an internal decomposition of the published proposition
`Langlands.GLParabolicRootWeightConeStatement` in
`Langlands.Representation.Classification.ParabolicConeStatement`.
It introduces proposition definitions only; it proves none of them.
The published target and its imported files remain unchanged.

`GLBlockConeNumericalConditions B C r q t` is exactly the conjunction of
monotonicity and surjectivity of `q`, the fiber-size equations, strict
antitonicity of `t`, the fiber-average equations, and the nonpositive
residual prefix sums from that target. It omits the matrix containments.
The fiber containing `i` is cut off inclusively at `i`, with the same sign
and real casts as in the published target.

`GLBlockConeExistenceStatement` asserts that these numerical witnesses exist
for every rank, shape and vector. No positivity of the total rank is needed:
a rank-zero shape has no positive blocks, and all witnesses can be empty.
This is a slightly stronger existence interface than the positive-rank
closing target.

`GLBlockConeUniquenessStatement` asserts that two sets of numerical
witnesses for the same fine shape and real vector have equal coarse
`BlockShape` structures. It does not require subgroup containments and does
not separately assert equality of the maps or exponent vectors. It also
allows zero rank.

`GLBlockCoarseningSubgroupStatement` separates the elementary matrix
consequence: a monotone surjection with the stated natural-number fiber-size
equations gives containment of the actual fine parabolic and embedded Levi
in their coarse counterparts, over every commutative ring of the arbitrary
universe `uR`. It requires no real vector or cone inequalities and no
positive-rank assumption. This is the reusable form needed by the maximal
cone argument.

`GLBlockConeAuxiliaryStatements` groups these three proof obligations as a
single proposition for interface review. Each component is independently
named so its proof can be developed and reviewed separately.

The provenance is internal: the first two interfaces factor the numerical
clauses of the existing Library target, and the third isolates its matrix
clause under precisely the numerical coarsening hypotheses. The zero-rank
extensions are elementary empty cases, not additional claims attributed to
Silberger. Their proofs, and the assembly of the original unique-existence
statement, remain separate obligations.
