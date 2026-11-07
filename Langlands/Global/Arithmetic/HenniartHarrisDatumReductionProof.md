# Henniart's Harris datum from the weight-one CM characters

Worker 84 wrote the proof pair; Worker 1690 adopted it and checked it against
the published prerequisites. The module proves `Langlands.Global.henniartHarrisDatum_of_halfWeight`:

`CMHalfWeightCharacterStatement.{0} → HenniartHarrisDatumStatement.{uF}`.

The theorem `Langlands.Global.henniartHarrisDatumOfHalfWeight` states it as the
exact target `HenniartHarrisDatumOfHalfWeightStatement.{uF}` of
`HenniartHarrisDatumReductionStatement`.

The proof combines two theorems. `henniartCommonBaseRealization`
(`HenniartCommonBaseRealizationProof`) gives the common CM field `E`, the
place `v₀`, the isomorphism `ι₀`, and for each `F'` a configuration with
`P.v = v₀` and `P.iso` equal to `ι₀` on `E`.
`HarrisDatum.harrisDatumCharacterRealization_of_halfWeight`
(`HarrisDatumCharacterRealizationProof`), at universes `uE = uE' = uL = 0`,
then gives the datum characters on that configuration. The universe-`0`
instance of the weight-one statement is the only hypothesis. No other
hypothesis or axiom is added.

The proof chooses `E`, `v₀` and `ι₀` before introducing `F'`, the normalized
reciprocity family `e`, or the character `χ₀`. For each intermediate `F'`, it
keeps the configuration and the equalities `P.v = v₀` and `P.iso = ι₀` on
`E`, and appends the datum and the unit-agreement conclusion supplied by the
character realization. The local field universe `uF` remains arbitrary.

This is an internal composition of the two published theorems. Their paired
Markdown explains their provenance in Henniart 2000, Sections 3.3–3.7, and
Harris 1998, Proposition 4.8. The present module adds only this composition;
its character agreement is on valuation units, exactly as the target states.
