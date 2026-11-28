# Determinants and pair factors of the relative generated isometry

`Langlands.Global.PoleComparison.relativeIsometryFactor` proves
`Langlands.Global.PoleComparison.RelativeIsometryFactorStatement.{uF,uW,uP,uE}`
at its four independent universe levels. Under the certified pole comparisons,
every generated positive isometry intertwines the determinant and central
character for every geometric reciprocity candidate. It gives the pair
L-factor and epsilon-factor identities for every nontrivial additive character
and every self-dual measure, with existence of a self-dual measure and a common
epsilon certificate for each local-constant system.

The proof applies `relativeIsometryFactorStatement_of_realContinuation_and_tests`
to `realLocalUniformUnequalContinuation` and the two real ordinary test theorems.
`realUnequalOrdinaryPlaceTests` is specialized to smaller groups of size at
least two. `realEqualOrdinaryPlaceTests` supplies the equal-rank tests for
groups of size at least two. The reduction supplies the rank-one cases of
these test hypotheses. [Real-place reduction](RelativeIsometryFactorRealReduction.md) ·
[Unequal-rank continuation](../RankinSelberg/RealLocalUniformUnequalContinuationProof.md) ·
[Unequal-rank tests](../RankinSelberg/RealUnequalOrdinaryPlaceTestsProof.md) ·
[Equal-rank tests](../RankinSelberg/RealEqualLastRowPlaceTestsProof.md)

The real and complex place results give the global Rankin–Selberg functional
equation for cuspidal pairs. The resulting finite-place gamma comparison gives
the tempered pair comparison on the unitary supports of the witnessed
generators. `relativeIsometryFactorStatement_of_tempered` extends the generator
identities to the signed spans and uses compatibility of degrees and
determinants to pass from the canonical additive character to each character
in the conclusion. This is the finite-relative form of the determinant and
pair-factor clauses of Henniart's Proposition 2.6 (a) and (b).
[Tempered reduction](RelativeIsometryFactorReduction.md) ·
[Target and source conventions](RelativeIsometryFactorStatement.md)
