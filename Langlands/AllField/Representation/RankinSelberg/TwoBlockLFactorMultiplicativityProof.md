# Two-block L-polynomial multiplicativity over every local field

Module `Langlands.AllField.Representation.RankinSelberg.TwoBlockLFactorMultiplicativityProof`.

`Langlands.AllField.RankinSelberg.twoBlockLFactorMultiplicativity` proves
`Langlands.AllField.RankinSelberg.TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW}`
(module `Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`)
with no additional premises. This is the all-field port of the Library's p-adic
statement `Langlands.RankinSelberg.TwoBlockLFactorMultiplicativityStatement`: JPSS 1983,
Theorem (3.1)(ii), for normalized induction from two blocks, in every rank order. The
field `F` is any field with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, so every nonarchimedean local field is covered,
including those of positive characteristic. The induction is
`(⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ`.

## Proof

This module is the all-field port of the Library module
`Langlands.Representation.RankinSelberg.TwoBlockLFactorMultiplicativityProof` (its
Markdown explains the proof and its provenance). Its last input, the full Proposition
(2.13) in the original, is changed as described below.

As in the original, the theorem is
`TwoBlockLVerifiedInputAssembly.twoBlockLFactorMultiplicativity_of_remainingInputs`
(all-field, module `TwoBlockLVerifiedInputAssembly`) applied to five closed theorems:

| Analytic input | Closed all-field theorem |
| --- | --- |
| Dominant rank, including equality | `twoBlockLDominantRank.{uF, max uF uV uW, max uF uV uW}` |
| Adjacent rank with first block of rank one | `twoBlockLAdjacentRank.{uF, max uF uV uW, max uF uV uW}` |
| Test rank one | `twoBlockLRankOne.{uF, max uF uV uW, max uF uV uW}` |
| Restricted reverse rank-one extension comparison | `rankOneExtensionLDivisibility.{uF, max uF uV uW, max uF uV uW}` |
| High-ramification vanishing, first member of rank one | `whittakerTypeHighlyRamifiedRankOneLVanishing.{uF, 0, max uF uV uW}` |

The only difference from the original is the last row. The original supplies the full
`whittakerTypeHighlyRamifiedLVanishing` (JPSS Proposition (2.13) for all ranks). The
all-field assembly takes instead the rank-one case
`WhittakerTypeHighlyRamifiedRankOneLVanishingStatement`, which is the only case its
descent uses (see the deviation section of
[TwoBlockLVerifiedInputAssembly](TwoBlockLVerifiedInputAssembly.md) and
[TwoBlockLConditionalAssembly](TwoBlockLConditionalAssembly.md)). It is proved over
every local field in
[WhittakerTypeHighlyRamifiedRankOneProof](WhittakerTypeHighlyRamifiedRankOneProof.md).
The other four theorems are from the all-field port, in the modules
`RankOneExtensionDivisibilityProof`, `TwoBlockAdjacentRankProof`,
`TwoBlockDominantRankProof` and `TwoBlockRankOneProof` under
`Langlands.AllField.Representation.RankinSelberg`.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, Theorem (3.1)(ii),
printed pages 404-405, with the descent of Section 7 (printed pages 438-443), which
uses Proposition (2.13). Section 0.3 (printed page 375) allows any nonarchimedean local
field. The Markdown of the original module gives the full provenance.
