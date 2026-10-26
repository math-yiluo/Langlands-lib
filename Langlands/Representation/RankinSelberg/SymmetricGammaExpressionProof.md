# Canonical symmetric gamma expression: proof

The theorem `Langlands.RankinSelberg.symmetricGammaExpression` proves the closed
`Langlands.RankinSelberg.SymmetricGammaExpressionStatement.{uF,uV,uW}`. The
field and the two representation carriers retain independent universes. All
positive ranks, equal ranks, and both orders of unequal ranks are included.

For the existing `PadicSymmetricGammaConstructionInput`, arbitrary certified
epsilon data `e`, original polynomial `P`, and dual polynomial `Pdual`, the
theorem characterizes every rational gamma certificate `G` by

```text
G = rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pdual.
```

The dual certificate uses the actual `inverseTransposePullback` representations,
the character `ψ.scale (-1)`, and the same supplied additive measure `ν.val`.
The theorem adds no nonvanishing, irreducibility, or analytic hypotheses to the
published target.

## Implemented proof

The supporting theorem
`IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput` treats an ordered
pair. It installs the canonical field structures and Borel structures, extracts
the rank inequality, original Whittaker types, and both analytic inputs from
the existing construction premise, and derives both dual Whittaker types with
`isOfWhittakerType_firstDual` and `isOfWhittakerType_secondDual`.

Both intrinsic polynomial certificates are specialized to the actual
`unipotentQuotientHaar`, using `unipotentQuotientHaar_isCompatible`. In equal
rank, `IsEqualRankEpsilonFactor.gammaFactor` supplies the universal gamma
certificate from these polynomials and the supplied epsilon certificate. In
strictly unequal rank, `IsUnequalRankEpsilonFactor.gammaFactor` performs the
same step for the full block family, including the complementary dual blocks.
The dual analytic input is applied to the transported nonzero functionals,
using the published nonzero-functional transport lemmas.
`LocalFactor.coe_residueReflection` identifies the actual reflection unit with
the inverse canonical residue cardinality.

The final theorem reduces the common larger-rank-first branch of the
construction input and all three supplied certificates. The ordered-pair
theorem certifies the displayed expression in either branch. The forward
implication then follows from `IsPadicSymmetricGammaFactor.unique`; the reverse
implication substitutes the stated equality into that certificate.

## Provenance and scope

The ordered-pair rank dispatch and specialization to nonzero dual functionals
adapt Worker 31's `gammaFactorOfAnalyticInput` assembly in `PadicGammaFactor`.
The present proof instead certifies the expression for the supplied arbitrary
epsilon and polynomial data. Worker 31 is credited as an adaptation coauthor.

This is an internal derived bridge between published Library interfaces. It
uses the existing proofs in `GammaFromWhittakerType`,
`EqualRankGammaFactor`, `UnequalRankGammaFactor`, `PadicPairFactors`, and
`LocalFactor.ResidueReflection`. It does not establish the analytic inputs,
epsilon existence, or the construction-input premise from bare
representations, and makes no additional rank-exchange claim.

The original mathematical source is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Section 2.1, printed pages 385–386 (PDF pages 20–21), gives Whittaker type
and dual/character conventions. Theorem 2.7, printed pages 390–391 (PDF
pages 25–26), gives the normalized generators, dual analytic conclusions,
and functional equations; section 2.12, printed page 403 (PDF page 38),
gives the larger-rank-first convention. These pages were read visually.
No source-specific errata file was found in the project literature or the
Library notes. The present arbitrary-certificate iff is derived packaging
of the conditional constructions and uniqueness, rather than a verbatim
theorem of the article.
