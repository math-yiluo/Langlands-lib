# Henniart's route with the standard inputs discharged

Author: Worker 4803. Module `Langlands.Correspondence.HenniartCorrespondenceReduction`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), all
independent.

## Statement: `SupercuspidalCorrespondenceHenniartReducedStatement.{uK, uW, uV}`

The implication

1. `RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV}` (local
   converse, Henniart 1993),
2. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`,
3. `StableCorrespondenceStatement.{uK, uW, uV, uW}`,
4. `UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW}` (items 2–4 are
   components of Worker 14's published `HenniartStableMapStatement`: Henniart
   2000, Théorème 3.1 with §§3.7–3.8, Théorème 4.2, and §4.4),
5. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (normalized local
   reciprocity in a common closure),
6. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family),
7. `RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}` (the JPSS
   unramified-twist law for pair epsilon factors)

implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField.{uK} p` there is exactly one supercuspidal
correspondence. Each hypothesis is a published Library proposition. The
statement asserts none of them.

The hypotheses are those of the published
`SupercuspidalCorrespondenceHenniartReductionStatement` (module
`HenniartExtensionReduction`), in the same order, without
`SupercuspidalUnitaryFiniteOrderTwistStatement` and
`ArithmeticPairUnramifiedTwistStatement`.

## Provenance

Internal. It is the published reduction (Henniart 2000, §4.4, printed p. 453,
PDF p. 15, with Henniart 1993, §4) with its two auxiliary hypotheses proved. Their
sources are recorded in `HenniartExtensionInputs.md`.

## Proof

`supercuspidalCorrespondenceHenniartReduced` applies
`supercuspidalCorrespondenceHenniartReduction` with
`supercuspidalUnitaryFiniteOrderTwist` (module `HenniartUnitaryTwistProof`) as its
fifth hypothesis and `arithmeticPairUnramifiedTwist` (module
`HenniartArithmeticTwistProof`) as its ninth. Standard axioms only.
