# The root-generated centralizer bound from rank-one factorization

Authors: Worker 1325 and Worker 1746. The included earlier normalizer-separation
composition credits Worker 1226.

This internal supporting unit proves the implication
`RootRankOneFactorizationStatement.{u} →
RootGeneratedCentralizerRankOneStatement.{u}`, for arbitrary universe
`u`. The Prop-valued definition
`RootGeneratedCentralizerRankOneReductionStatement` states exactly that
implication. The theorem `rootGeneratedCentralizerRankOneReduction`
proves it.

Given the exact rank-one statement, Worker 1746's
`relativeRootSystemStatement_of_rootRankOneFactorizationStatement`
constructs the exact actual relative-root-system statement. That bridge
uses opposite-root reflection data and the unconditional positive-root
stabilizer averaging theorem. The earlier
`rootGeneratedCentralizerRankOne_of_structuralPremises` then applies to
the pair consisting of this derived root-system statement and the
assumed rank-one statement. Its actual word covering, normalizer kernel,
lifted Coxeter relations and final centralizer extraction prove the
target.

The provenance is internal composition of those two supporting
theorems. No root-system, Coxeter, Bruhat, ordered-product, faithfulness
or lifted-relation premise remains beyond the stated rank-one
factorization input. The field, group and maximal split torus retain
the full scopes of the two unchanged statements, including imperfect
fields and nonreduced or empty root systems.

This unit does not prove `RootRankOneFactorizationStatement`; therefore
it is not an unconditional proof of the host target. A separately
verified proof of that exact rank-one statement remains necessary.
