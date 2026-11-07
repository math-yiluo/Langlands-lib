# Epsilon factors of all pairs of square-integrable blocks

Author: Worker 1790. Module
`Langlands.Representation.RankinSelberg.LanglandsPairEpsilonBlockExistence`,
namespace `Langlands.RankinSelberg`.

This module proves the analytic block input of the published reduction
`langlandsPairEpsilonFactorExistence_of_classification` (module
`LanglandsPairEpsilonFactorExistenceStatement`): every pair of blocks of two
square-integrable Langlands data has its JPSS epsilon factor. It defines
the resulting product factor of any two such data, without an existence
hypothesis. It then combines the block input with that reduction, so that
`LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` follows from
square-integrable exhaustion and classification alone. Exhaustion and
classification are **not** proved here; the final theorem keeps them as
explicit hypotheses and is not a proof of the existence statement.

## Results

1. `essentiallySquareIntegrable_isGeneric F T n π hπi hπ ψ`. For
   `T : F.TopologicalData`, every
   `π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)`
   that is irreducible and satisfies the analytic predicate
   `T.IsEssentiallySquareIntegrable π.representation` is
   `Whittaker.IsGeneric ψ n π.representation` for every
   `ψ : UnitaryAdditiveCharacter F.Carrier`. No unitarity or invariant form
   is assumed. This extends the published
   `Langlands.Classification.squareIntegrableGenericity` from unitary
   square-integrable to essentially square-integrable representations;
   the proof is the same.
2. `essentiallySquareIntegrable_epsilonFactorExists F ψ ν hm hk π σ ...`.
   For `ψ` and `ν : LocalFactor.PadicAbelian.SelfDualHaar
   F.canonicalTopologicalData ψ`, positive ranks `0 < m`, `0 < k`, and
   irreducible essentially square-integrable
   `π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)`,
   `σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear k F.Carrier)`, it
   proves `∃ e, IsPadicRankEpsilonFactor F ψ ν.val π.representation
   σ.representation e`. The ranks are arbitrary, in either order.
3. `squareIntegrableDataEpsilonExistence F ψ ν d d'`. For all ranks `n`, `t`
   and all
   `d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData n`,
   `d' : SquareIntegrableLanglandsDatum.{max uF uW, uF} F.canonicalTopologicalData t`,
   it proves `SquareIntegrableDataEpsilonExistence F ψ ν.val d d'`: every
   block pair `(d.blocks i, d'.blocks j)` has an epsilon factor. The datum
   universes are the saturated carrier universes used by the input `hb` of
   the reduction. Specialized to ranks `r + 1` and `t + 1` this is exactly
   `hb`.
4. `squareIntegrableDataEpsilonFactorOfBlocks F ψ ν d d'`. For the same
   data, this definition is the subtype element
   `{e : ℂˣ × ℤ // IsSquareIntegrableDataEpsilonFactor F ψ ν.val d d' e}`
   given by the published constructor `squareIntegrableDataEpsilonFactor`
   applied to (3). Its value is `epsilonFactorProduct` of chosen block
   factors, the product of the epsilon factors of all block pairs. By
   `IsSquareIntegrableDataEpsilonFactor.unique` the value does not depend on
   these choices. No existence input is a hypothesis.
5. `langlandsPairEpsilonFactorExistence_of_exhaustion_classification hex hcl`.
   With the hypotheses `hex` and `hcl` of
   `langlandsPairEpsilonFactorExistence_of_classification`, word for word:
   `SquareIntegrableLanglandsExhaustion` and
   `SquareIntegrableLanglandsClassification` at `.{uF, uV}` and `.{uF, uW}`
   for every prime and every `F : PadicField.{uF} p` with its canonical
   topological data. It concludes
   `LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}`. The universes
   `uF`, `uV`, `uW` stay independent.

## Implemented proof

**Genericity (1).** Apply the proved theorem
`Classification.segmentEssentialSquareIntegrableClassification` at rank
`n + 1` to the irreducible `π`. Its forward direction turns the hypothesis
`T.IsEssentiallySquareIntegrable π.representation` into an actual segment
`Δ`, an equality `hΔ : Δ.degree = n + 1` and the strong head relation
`T.IsSegmentHead Δ (hΔ.symm ▸ π)`. Build the one-segment
`SegmentProductDatum` with segment `Δ` and block `hΔ.symm ▸ π`. The head
relation gives `HasSegmentHeads`; its multisegment is the singleton `{Δ}`,
which is unlinked by `Segment.not_isLinked_self`.
`SegmentProductOrderedAssembly.singletonIso` and a private helper
`rankCastCancelIso` give an isomorphism from the singleton induced
representation to `π`. The helper eliminates the equality `h : a = b` and
returns the identity isomorphism. The reverse direction of the proved theorem
`Classification.genericSegmentProductExhaustion` for `ψ`, `n`, `π` then gives
genericity. This is the argument of
`Classification.squareIntegrableGenericity`, which applies
`IsSquareIntegrable.isEssentiallySquareIntegrable` first. Here the essential
hypothesis is given directly.

**Pair factors (2).** Install `F.canonicalTopologicalData.topology` and case
on `m` and `k`. Rank zero contradicts `0 < m` or `0 < k`. At ranks `r + 1` and
`t + 1`, `IsPadicRankEpsilonFactor` unfolds by definition to
`IsPadicSymmetricEpsilonFactor`. The published
`genericSymmetricEpsilonData_isPadic F ψ ν.val ν.property π σ hπ hσ`
(module `PadicSymmetricEpsilonFactor`) proves this for the explicit data
`genericSymmetricEpsilonData`, in both rank orders. Its genericity inputs
come from (1), at carrier universes `max uF uV` and `max uF uW`. The
self-duality input `ν.property` is the property of the supplied
`SelfDualHaar` measure. The proof does not choose any measure or assert that
one exists.

**Block input (3).** For blocks `i` and `j`, apply (2) to `d.blocks i` and
`d'.blocks j`. The datum fields provide the positivity of the block sizes
(`d.shape.positive`), irreducibility (`d.irreducible`) and essential
square-integrability (`d.essentiallySquareIntegrable`). The unitary-exponent
data and the exponent order of the data are not used.

**Data factor (4).** Apply `squareIntegrableDataEpsilonFactor F ψ ν.val d d'`
to the existence proof (3).

**Reduction (5).** Apply
`langlandsPairEpsilonFactorExistence_of_classification hex hcl` with (3) as
its block input `hb`.

## Dependencies

All inputs are published Library theorems, imported by Lean name:

- `Classification.segmentEssentialSquareIntegrableClassification`
  (`SegmentEssentialSquareIntegrableClassificationProof`);
- `Classification.genericSegmentProductExhaustion`
  (`GenericSegmentProductExhaustionProof`), reverse direction only;
- `SegmentProductOrderedAssembly.singletonIso`
  (`SegmentProductOrderedAssembly`);
- `genericSymmetricEpsilonData_isPadic` (`PadicSymmetricEpsilonFactor`),
  which rests on the published JPSS equal- and unequal-rank functional
  equation constructions;
- `squareIntegrableDataEpsilonFactor` (`LanglandsFactors`), used in (4);
- `langlandsPairEpsilonFactorExistence_of_classification`
  (`LanglandsPairEpsilonFactorExistenceStatement`), used only in (5).

The remaining inputs `SquareIntegrableLanglandsExhaustion` and
`SquareIntegrableLanglandsClassification` are published propositions of
`Classification/MultisegmentClassificationStatement`. Their proofs are not
part of this module.

## Provenance

This is a derived assembly of published results. The mathematical content
is Henniart 2002, §2.8, printed p.596: the epsilon factor of a pair is the
product of the JPSS epsilon factors `ε(s, π_i × π'_j, ψ)` of the
essentially square-integrable blocks. These block factors exist because
essentially square-integrable representations are generic. The
`LanglandsPairEpsilonFactorExistenceStatement.md` audit records this source
(source ID `henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`). The
genericity route follows the paired Markdown of
`SquareIntegrableGenericityProof`, which cites Zelevinsky 1980 §§9.1, 9.3
and Theorem 9.7(a). No new literature claim is made here.

## Lean checks

`lean_check` of the module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reports 0 errors and 0 warnings.
Inspecting `Langlands.RankinSelberg.squareIntegrableDataEpsilonFactorOfBlocks`
shows a definition with universe parameters `uF`, `uV`, `uW`. Inspecting
`Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence_of_exhaustion_classification`
shows a theorem with universe parameters `uF`, `uV`, `uW` and axioms
`propext`, `Classical.choice`, `Quot.sound`.
