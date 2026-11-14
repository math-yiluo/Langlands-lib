# NYLL M103 DVF Basic: characteristic instance and successive maximal-ideal quotients

This module adapts six source declaration commands of
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean)
(inventory module M103): the characteristic instance on valuation subrings
(M103.001) and the successive ideal-power quotient data `m^n / m^(n+1)` of a
chosen discrete valuation field (M103.031, M103.032, M103.033, M103.034 and
M103.036). It also records the focused check that discharges the three
source instance aliases M103.004, M103.005 and M103.006 by canonical Mathlib
instances, without new declarations.

The bundle `DVF` and its abbreviations `valuationSubring` and `maximalIdeal`
are imported from the published
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
(source units M103.002, M103.003 and M103.007); this module does not redefine
them.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, whose
SHA-256 is
`abda99fd0b28655e1317ae832e8c94c7431b7229d99cf07138d89c4a5c953493`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The public port partition reports no patch10 modification of this file, and
no applicable erratum was found in the project's errata lookup.

## Exact source correspondence

Write `S = ValuationTheory` for the original namespace and
`T = Langlands.NYLL.ValuationTheory` for the adapted one. Lines are those of
the pinned source file, including the docstring.

| Unit | Original declaration | Source lines | Adapted declaration |
| --- | --- | --- | --- |
| M103.001 | instance `S.ValuationSubring.charP` | 27–30 | instance `T.ValuationSubring.charP` |
| M103.004 | instance `S.DiscreteValuationField.DVF.valuationSubring.commRing` | 57–60 | no new declaration: Mathlib's `ValuationSubring.instCommRingSubtypeMem` (see below) |
| M103.005 | instance `S.DiscreteValuationField.DVF.valuationSubring.isLocalRing` | 62–65 | no new declaration: Mathlib's `ValuationSubring.isLocalRing` (see below) |
| M103.006 | instance `S.DiscreteValuationField.DVF.valuationSubring.isDomain` | 67–70 | no new declaration: Mathlib's `ValuationSubring.instIsDomainSubtypeMem` (see below) |
| M103.031 | abbrev `S.DiscreteValuationField.DVF.maximalIdealPowSuccSubmodule` | 318–323 | abbrev `T.DiscreteValuationField.DVF.maximalIdealPowSuccSubmodule` |
| M103.032 | def `S.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot` | 325–328 | def `T.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot` |
| M103.033 | instance `S.DiscreteValuationField.DVF.maximalIdealPowSuccQuotAddCommGroup` | 330–337 | instance `T.DiscreteValuationField.DVF.maximalIdealPowSuccQuotAddCommGroup` |
| M103.034 | instance `S.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule` | 339–346 | instance `T.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule` |
| M103.036 | def `S.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk` | 361–370 | def `T.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk` |

The intervening source declaration M103.035
(`maximalIdealPowSuccQuotConcreteLinearEquiv`, lines 348–359) is not used by
any of these declarations or by the statement targets of this task, and is not
ported here.

## Declarations

In the following, `K : Type u` carries a supplied `[Field K]`, and
`F : DVF.{u, v} K` is a chosen discrete valuation field with independent
universe `v` for its value group. Write `O = F.valuationSubring` (the type of
`x : K` with `F.valuation x ≤ 1`) and `m = F.maximalIdeal`, the maximal ideal
`IsLocalRing.maximalIdeal O`.

### `T.ValuationSubring.charP` (M103.001)

```lean
instance charP {K : Type u} [Field K] (R : ValuationSubring K) (p : ℕ) [CharP K p] :
    CharP R p :=
  CharP.subring K p R.toSubring
```

For any valuation subring `R` of a field `K` of characteristic `p`, the ring
`R` (the subtype of its elements) has characteristic `p`. The body is Mathlib's
`CharP.subring` applied to the underlying subring `R.toSubring`. It is a global
instance, as in the source. Mathlib provides `CharP` instances for subtypes of
`Subring`s and `Subsemiring`s but none for the subtype of a `ValuationSubring`,
and the Library has none either; since `CharP` is a `Prop`-valued class, the new
instance cannot create a data diamond.

### `maximalIdealPowSuccSubmodule F n` (M103.031)

The reducible `Submodule O ↥(m ^ n)` obtained by pulling the ideal `m ^ (n + 1)`
(as a submodule of `O`) back along the inclusion `Submodule.subtype` of
`m ^ n` into `O`. Its elements are the elements of `m ^ n` that lie in
`m ^ (n + 1)`.

### `MaximalIdealPowSuccQuot F n` (M103.032)

The `Type u` defined as the quotient
`↥(m ^ n) ⧸ maximalIdealPowSuccSubmodule F n`, that is `m^n / m^(n+1)`. It is
a semireducible `def`, as in the source, so instance search does not see
through it.

### `maximalIdealPowSuccQuotAddCommGroup F n` and `maximalIdealPowSuccQuotModule F n` (M103.033, M103.034)

Global instances, as in the source, giving `MaximalIdealPowSuccQuot F n` the
additive commutative group structure and the `O`-module structure of the
submodule quotient. Each body is the source tactic block
`change …; infer_instance`, which unfolds the `def` and uses Mathlib's quotient
instances. The type `MaximalIdealPowSuccQuot` is new, so no other instance on it
exists in Mathlib or the Library.

### `maximalIdealPowSuccQuotMk F n` (M103.036)

The `O`-linear map `↥(m ^ n) →ₗ[O] MaximalIdealPowSuccQuot F n` given by the
source tactic block, which unfolds the target type and is exactly
`Submodule.mkQ (maximalIdealPowSuccSubmodule F n)`, the quotient map.

## Canonical instance reuse of M103.004–M103.006

The three source instances at lines 58, 63 and 68 are named aliases for
Mathlib's canonical instances on the valuation subring
`F.valuation.valuationSubring`. In the published stem, `F.valuationSubring` is
a reducible abbreviation of that subtype, so instance search finds the Mathlib
instances directly. Following the stem module's documented decision, this
module introduces no aliases. The following replacements are confirmed by the
`example` commands at the end of the Lean file, each with the complete source
telescope `{K : Type u} [Field K] (F : DVF.{u, v} K)`:

| Unit | Source body | Replacement and focused check |
| --- | --- | --- |
| M103.004 | `ValuationSubring.instCommRingSubtypeMem F.valuation.valuationSubring` | The synthesized `CommRing F.valuationSubring` equals the source body by `rfl`. |
| M103.005 | `ValuationSubring.isLocalRing F.valuation.valuationSubring` | The source body has type `IsLocalRing F.valuationSubring`, and instance search synthesizes this type. |
| M103.006 | `ValuationSubring.instIsDomainSubtypeMem F.valuation.valuationSubring` | The source body has type `IsDomain F.valuationSubring`, and instance search synthesizes this type. |

`IsLocalRing` and `IsDomain` are `Prop`-valued, so any two instances agree by
proof irrelevance; for the data-carrying `CommRing` the check confirms that the
synthesized instance is the source construction. The `example` commands add no
constants to the environment.

## Adaptation and modifications

Worker 171 made the following modifications on 14 November 2026:

- The namespaces are prefixed with `Langlands.NYLL`; the source nesting
  `ValuationTheory` › `ValuationSubring` and
  `ValuationTheory` › `DiscreteValuationField` › `DVF`, the
  `noncomputable section`, the `universe u v` command and the section variable
  `{K : Type u} [Field K]` are retained.
- The declarations above keep their universes, complete parameter and
  instance telescopes, binder kinds, docstrings, instance attributes and bodies
  (including the tactic blocks of M103.033, M103.034 and M103.036) unchanged.
  The source section comment for the successive quotients is retained.
- Only the selected units are extracted. The source data M103.002, M103.003
  and M103.007 is imported from the published stem module rather than
  redefined; the source aliases M103.004–M103.006 are replaced by canonical
  Mathlib instances, with the focused checks described above added as
  `example` commands.
- A modification header and a module docstring are added.

The imports are exactly:

- `Mathlib.Algebra.CharP.Subring` (source import, for `CharP.subring`);
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
  (the published `DVF`, `valuationSubring` and `maximalIdeal`), which imports
  the other three Mathlib modules imported by the source file.

Before authoring, the Library and the approved Mathlib were searched for these
declarations; none of them already existed. No other worker's draft is copied.
This support unit asserts no host reciprocity, Tate, cup-product, transfer or
class-formation result.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved; authors: Naganori
Yamaguchi (assisted by OpenAI Codex). The source is released under Apache-2.0.
The Library's [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) copies remain unchanged, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean file's second header comment prominently records the modifications.
