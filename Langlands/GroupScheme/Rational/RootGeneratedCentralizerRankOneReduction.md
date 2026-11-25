# The root-generated centralizer bound from rank-one factorization

This internal supporting module proves the implication
`RootRankOneFactorizationStatement.{u} →
RootGeneratedCentralizerRankOneStatement.{u}`, for arbitrary universe
`u`. The Prop-valued definition
`RootGeneratedCentralizerRankOneReductionStatement` states exactly that
implication. The theorem `rootGeneratedCentralizerRankOneReduction`
proves it.

Given the exact rank-one statement,
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

This module does not prove `RootRankOneFactorizationStatement`; therefore
it is not by itself an unconditional proof of
`RootGeneratedCentralizerRankOneStatement`. The exact rank-one statement is
proved by `rootRankOneFactorization` (module
`Rational.RootRankOneFactorizationProof`), and the unconditional
`rootGeneratedCentralizerRankOne` is in `Rational.RootGeneratedCentralizerRankOneProof`.
