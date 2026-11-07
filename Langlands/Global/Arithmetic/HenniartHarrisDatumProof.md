# Henniart's Harris datum and the datum characters

Worker 84 and Worker 1690. Worker 1690 adopted Worker 84's supplied Lean
proof unchanged and checked it against the published prerequisites. The module
proves two unconditional theorem statements, with the local hypotheses
quantified inside their respective target propositions.

`Langlands.Global.henniartHarrisDatum` proves the exact target
`HenniartHarrisDatumStatement.{uF}` of `HenniartHarrisDatumStatement`. The
target says the following. For a finite extension `M` of a p-adic field `F`,
there is one CM number field `E` with a place `v₀` and a continuous isomorphism
`ι₀ : E_{v₀} ≅ F`. For every intermediate field `F'` of `M/F`, every normalized
reciprocity family and every continuous character `χ₀` of `F'ˣ`, there are a
paired-place configuration over `E` at `v₀` and data of Harris's
Proposition 4.8 on it. The datum character `χ` at `P` equals `χ₀` on the units
of `F'`.

The proof applies the published reduction
`henniartHarrisDatumOfHalfWeight : HenniartHarrisDatumOfHalfWeightStatement.{uF}`
(`HenniartHarrisDatumReductionProof`) to the published
`cmHalfWeightCharacter : CMHalfWeightCharacterStatement.{0}`
(`CMHalfWeightCharacterProof`). The reduction combines the common-base
realization `henniartCommonBaseRealization` with the character realization on
each configuration.

`Langlands.Global.harrisDatumCharacterRealization` proves
`HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL}`, the datum
characters on every paired-place configuration. It applies
`harrisDatumCharacterRealizationOfHalfWeight`
(`HarrisDatumCharacterRealizationProof`) to `cmHalfWeightCharacter.{uE'}`.

Both proofs only compose published theorems. The literature for the targets
(Henniart 2000 §§3.3–3.7, Harris 1998 Proposition 4.8, Harris–Taylor 2001
Proposition VII.2.7 and Corollary VII.2.8) is cited in the Markdown of the
statement modules and of the composed proofs.

The main application specializes the CM-character theorem to global universe
`0`, as required by `HenniartHarrisDatumOfHalfWeightStatement`, and preserves
arbitrary local universe `uF`. Thus `E`, `E'` and `L` are in `Type`, while the
p-adic field has the universe required by the target. The reduction chooses
`E`, `v₀` and `ι₀` before introducing `F'`, `e` and `χ₀`; this application
retains their common-base quantifier order and all completion-compatibility
and valuation-unit conclusions.
