# Splitting of tori over separably closed fields

`Langlands.GroupScheme.toriAreSplit_of_isSepClosed` proves `ToriAreSplit k`
for every separably closed field `k` in any universe. It applies the published
coalgebra spanning theorem through
`SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites`.

This module consolidates the declaration previously in
[`AlgebraicFundamentalGroupWeyl`](../AlgebraicFundamentalGroupWeyl.md)
with the identical statement in
[`OppositeFactorPairsFromStructuralStatements`](../Reductive/OppositeFactorPairsFromStructuralStatements.md).
The proof is the latter module's unchanged coalgebra assembly.
Both consumers import this single declaration. No root-datum existence,
rank-one cell, or root-line proof is added to its dependencies.
