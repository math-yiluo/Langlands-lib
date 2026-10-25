# Chosen discrete valuation field and residue data

This module provides the data bundle
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF` and its four basic
valuation-ring and residue-data abbreviations. It adapts only lines 37–87 of
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean#L37-L87),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.

The original is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`);
the accompanying attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The selected original is readable under the registered snapshot's
`n-yamaguchi-0729--ClassFieldTheory/source/` directory. No applicable erratum
was found in the project's published errata lookup. The previously recorded
nine-file compatibility patch does not modify this source file.

## Bundle and fields

Let `K : Type u` carry a supplied `[Field K]`. A term `F : DVF.{u, v} K`
contains the following four fields, in source order.

| Projection, relative to `DVF` | Type and meaning |
| --- | --- |
| `ValueGroup` | A chosen `Type v`, the multiplicative value group with zero. |
| `instValueGroup` | A supplied `LinearOrderedCommGroupWithZero F.ValueGroup`. |
| `valuation` | A chosen `Valuation K F.ValueGroup`, using `F.instValueGroup`. |
| `instRankOneDiscrete` | A supplied proof of `F.valuation.IsRankOneDiscrete`. |

Both `DVF.instValueGroup` and `DVF.instRankOneDiscrete` retain their source
instance attributes. They expose the structures already stored in `F`; the
bundle does not manufacture a valuation or a discreteness proof. Mathlib's
`Valuation.IsRankOneDiscrete` asserts the existence of a unit `γ` in the
value group whose integer powers equal the valuation's value subgroup and
such that `γ < 1`. In particular, the bundle does not require the valuation
to be surjective onto every element of the chosen ambient value group.

The universe levels `u` and `v` are independent. The field lives in `Type u`,
the value group in `Type v`, and all four residue-data abbreviations below
retain the source field universe. `DVF` is a structure with an explicit
bundle argument in its operations, rather than a typeclass choosing a
valuation for every field. Its constructor and generated structure
projections are those of this four-field structure.

## Basic data

In the following table all names are relative to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`.

| Declaration | Type and definition |
| --- | --- |
| `valuationSubring F` | The `Type u` underlying `F.valuation.valuationSubring`. Its elements are elements `x : K` satisfying `F.valuation x ≤ 1`. This is a type abbreviation, not a new bundled subring. |
| `maximalIdeal F` | An `Ideal F.valuationSubring`, defined as `IsLocalRing.maximalIdeal F.valuationSubring`. |
| `residueField F` | The `Type u` given by `IsLocalRing.ResidueField F.valuationSubring`, the quotient of the valuation ring by its maximal ideal. |
| `residueMap F` | A `RingHom F.valuationSubring F.residueField`, defined as `IsLocalRing.residue F.valuationSubring`, the canonical quotient map. |

These are reducible `abbrev` declarations. Ring operations on the valuation
ring are inherited from the subring of `K`; the maximal ideal, residue field
and residue map are the existing Mathlib constructions, with no additional
choices of ideals or ring structures.

## Exact source correspondence and canonical instances

Write `S = ValuationTheory.DiscreteValuationField` for the original namespace
and `T = Langlands.NYLL.ValuationTheory.DiscreteValuationField` for the adapted
namespace.

| Original declaration and starting line | Adapted declaration or reuse |
| --- | --- |
| `S.DVF`, line 37 | `T.DVF`, with all four fields and their order unchanged. |
| `S.DVF.instValueGroup`, field line 41 | `T.DVF.instValueGroup`, retaining its instance attribute from line 47. |
| `S.DVF.instRankOneDiscrete`, field line 45 | `T.DVF.instRankOneDiscrete`, retaining its instance attribute from line 47. |
| `S.DVF.valuationSubring`, line 54 | `T.DVF.valuationSubring`, with the same body and `Type u` result. |
| `S.DVF.valuationSubring.commRing`, line 58 | No new alias: Mathlib's `ValuationSubring.instCommRingSubtypeMem F.valuation.valuationSubring` supplies `CommRing F.valuationSubring`. |
| `S.DVF.valuationSubring.isLocalRing`, line 63 | No new alias: Mathlib's `ValuationSubring.isLocalRing F.valuation.valuationSubring` supplies `IsLocalRing F.valuationSubring`. |
| `S.DVF.valuationSubring.isDomain`, line 68 | No new alias: Mathlib's `ValuationSubring.instIsDomainSubtypeMem F.valuation.valuationSubring` supplies `IsDomain F.valuationSubring`. |
| `S.DVF.maximalIdeal`, line 73 | `T.DVF.maximalIdeal`, with the same body. |
| `S.DVF.residueField`, line 77 | `T.DVF.residueField`, with the same body and `Type u` result. |
| `S.DVF.residueField.field`, line 81 | No new alias: Mathlib's `IsLocalRing.ResidueField.field F.valuationSubring` supplies `Field F.residueField`. |
| `S.DVF.residueMap`, line 85 | `T.DVF.residueMap`, with the same body and ring-homomorphism type. |

The names of the four omitted aliases are deliberately absent from the
adapted namespace. Instance search unfolds the type abbreviations and uses
the canonical Mathlib instances listed in the table. The source aliases
were wrappers for precisely these instances. The only instance attributes
added by this module belong to the two fields of the new bundle.

The module imports only
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Mathlib.RingTheory.Valuation.Discrete.Basic` and
`Mathlib.RingTheory.Valuation.LocalSubring`. There are no NYLL imports.
The source `Mathlib.Algebra.CharP.Subring` import and the `charP` instance
at line 28 are excluded. All source theorems from line 90 onward, higher
ideal quotients, completion and extension data are excluded. This
publication contains no new theorem asserting a DVR property and does not
identify the chosen valuation with any separately supplied host valuation.

## Attribution and modifications

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex). The source is
released under Apache-2.0. Copies of the original
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) accompany this extraction.
The upstream NOTICE has no source-specific entry for the selected
`DiscreteValuationField/Basic.lean`; its notices for other extracted source
files remain preserved in the unmodified copy.

Worker 384 extracted the selected data, added the `Langlands.NYLL`
namespace prefix, removed the unused characteristic import and all content
outside the selected unit, omitted the four redundant instance aliases,
and wrote this source map and documentation on 25 October 2026. The Lean
header prominently records these modifications. No external dependency
closure was copied into this module.
