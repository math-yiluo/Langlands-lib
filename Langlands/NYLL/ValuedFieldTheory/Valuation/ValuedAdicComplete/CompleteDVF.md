# Packaging a complete rank-one discrete valued field

This module adapts exactly M247.004,
`ValuationTheory.Valuations.completeDVFOfCompleteValuedField`, from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean`, lines 140–155](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean#L140-L155),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its adapted name is
`Langlands.NYLL.ValuationTheory.Valuations.completeDVFOfCompleteValuedField`.
This is a noncomputable structural definition with proof fields.

## Parameters and result

For independent universes `u` and `v`, the complete parameter telescope is
`{K : Type u} [Field K] {Gamma : Type v}
[LinearOrderedCommGroupWithZero Gamma] [Valued K Gamma]
[(Valued.v : Valuation K Gamma).IsRankOneDiscrete] [CompleteSpace K]`.
The result is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`.

`CompleteSpace K` uses the uniformity supplied by the given `Valued K Gamma`
instance. The definition retains this instance and introduces no topology or
uniformity parameters or replacement structures. The ordered value group need
not be the entire image of the valuation.

The returned bundle has these fields:

| Field | Stored data |
| --- | --- |
| `ValueGroup` | Exactly the supplied `Gamma : Type v`. |
| `instValueGroup` | The supplied `LinearOrderedCommGroupWithZero Gamma` instance, inferred by structure elaboration. |
| `valuation` | Exactly the supplied `Valued.v : Valuation K Gamma`. |
| `instCompleteDiscrete` | The published `Valuation.IsCompleteDiscrete` predicate, containing the supplied rank-one-discrete witness and the imported adic-completeness proof. |

Write `val = (Valued.v : Valuation K Gamma)` and
`A = val.valuationSubring`. The last field stores `isRankOneDiscrete :=
inferInstance` and
`isAdicComplete := rankOneDiscreteValuationSubring_isAdicComplete`.
The latter theorem proves
`IsAdicComplete (IsLocalRing.maximalIdeal A) A` for the actual valuation
subring and its canonical maximal ideal. Its arguments are inferred from the
same supplied field, ordered group, valuation, discreteness and completeness
instances. The constructor adds no adic-completeness premise.

## Reuse and imports

The two direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`,
  supplying the existing `CompleteDVF` and `Valuation.IsCompleteDiscrete`.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteProof`,
  supplying the published
  `Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete`.

Neither module imports the other. The first supplies the bundle and the
second the completeness proof, so both imports are needed by this extraction.
Their published import closures supply the Mathlib valuation and completeness
APIs. No external NYLL repository module is imported.

The source uses `CompleteDVF` and `rankOneDiscreteValuationSubring_isAdicComplete`
under `ValuationTheory`; this extraction reuses their published counterparts
under `Langlands.NYLL.ValuationTheory`. All constructor fields and parameter
binders otherwise follow the original. The P3 compatibility patch in the
port plan concerns M247.002, already encapsulated by the imported theorem.
The constructor requires no compatibility proof change.

This unit adds no theorem or global instance. M247.001–.003 proofs,
Henselian/DVF projections, local-field packaging, chosen finite extensions,
integer-ring comparisons and reciprocity are outside its scope.

## Development checks

The focused module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with zero errors or warnings.
A separate private check prints the complete unapplied definition and verifies
the displayed telescope, independent levels `[u,v]`, and `CompleteSpace` for
the supplied `Valued.toUniformSpace`. Reducible projection examples check every
row of the field table and the exact adic-completeness conclusion. Declaration
inspection finds only `propext`, `Classical.choice` and `Quot.sound`.
These checks establish compilation and the stated data correspondence;
independent semantic review and publication are separate.

## Attribution and modifications

The complete 158-line original was read, including the preceding topology and
completeness proofs. Its SHA256 is
`183b8dd3fb4910ec7378d280839436826d06929fa4e8081dd460e89cbd05d5fb`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-specific errata directory exists in the workspace, project notes or
the Library used for this extraction.

The original copyright and author header is retained verbatim. The inherited,
unmodified [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values are,
respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected source file has no entry in the original NOTICE.

Worker 384 extracted the single constructor, added the `Langlands.NYLL`
namespace prefix, made the Mathlib `Valuation` reference explicitly rooted,
replaced the original imports by the two published modules above, and wrote
this explanation on 29 October 2026. Worker 106 supplied routing only.
No unpublished implementation or draft from another worker was reused.
