# Simple approximation of a pure stratum: proof

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, (2.4.1)(i), printed p. 65 (PDF p. 77), with its proof, printed pp. 66–71 (PDF pp. 78–83).

## Statement

`pureStratumSimpleApproximation : PureStratumSimpleApproximationStatement` proves the proposition of the module `PureStratumSimpleApproximationStatement`: over a nonarchimedean local field `F` and a finite-dimensional `F`-vector space `V`, every pure stratum `S` has an equivalent simple stratum `T` with `T.chain = S.chain`, `T.n = S.n`, `T.r = S.r`, such that `elementRamificationIndex F T.b` divides `elementRamificationIndex F S.b` and `elementResidueDegree F T.b` divides `elementResidueDegree F S.b`. The universes of `F` and `V` are independent, as in the statement.

## Proof

The theorem applies `pureStratumSimpleApproximation_of_premises` (module `PureStratumApproximationFromPremises`), which carries out the argument of the source from three propositions, to their proofs:

- `topNonsplitPremise : TopNonsplitPremise` (module `PureStratumTopNonsplitProof`), BK93 (2.3.11);
- `nonsplitRefinement : NonsplitRefinementPremise` (module `NonsplitRefinementProof`), BK93 (2.3.4), used at the universes of `F` and `V` and a second time with both universes equal to that of `V`, for fields generated inside `End_F(V)`;
- `splitObstructionPremise : SplitObstructionPremise` (module `SplitObstructionProof`), BK93 (2.3.12).

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
