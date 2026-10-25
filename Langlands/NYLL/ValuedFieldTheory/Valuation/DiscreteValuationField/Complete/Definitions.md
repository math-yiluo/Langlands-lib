# Complete discrete valuation predicate and chosen bundle

This module adapts the two structural declarations M107.001 and M107.006 from
Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file has SHA-256
`509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`.
The selected declarations and their instance attributes occupy lines 28–36
and 99–110. The source context through line 190 was read, including the
intervening theorems and later forgetful projections.

The original is retained under the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the project's errata lookup.
This source file has no modification in the recorded patch10.

## The structural predicate

All adapted names below are in
`Langlands.NYLL.ValuationTheory.DiscreteValuationField`.
For independent universes `u` and `v`, a field `K : Type u`, an ordered
commutative group with zero `Gamma : Type v`, and an actual Mathlib valuation
`val : _root_.Valuation K Gamma`, the class
`Valuation.IsCompleteDiscrete val : Prop` has exactly these fields:

| Field | Type |
| --- | --- |
| `isRankOneDiscrete` | `val.IsRankOneDiscrete` |
| `isAdicComplete` | `IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring` |

The field and value-group parameters and their structures are implicit,
and `val` is explicit. The class stores proofs of two existing Mathlib
predicates. `Valuation.IsRankOneDiscrete` requires a value-group unit below
one whose integer powers generate the valuation's value subgroup.
`IsAdicComplete I R` requires that the ring, as a module over itself, be
Hausdorff and precomplete for powers of `I`. Here `R` is exactly the actual
valuation subring of `val`, and `I` is its canonical local-ring maximal
ideal. The canonical Mathlib ring, local-ring and self-module instances
are used.

The projection `Valuation.IsCompleteDiscrete.isRankOneDiscrete` retains its
source instance attribute. The `isAdicComplete` proof remains an ordinary
field projection, as in the source class. Declaring this predicate supplies
no instance of completeness for an arbitrary valuation.

## The chosen bundle

For a field `K : Type u`, `CompleteDVF.{u, v} K` is a structure with exactly
four fields, in source order:

| Projection, relative to `CompleteDVF` | Type and role |
| --- | --- |
| `ValueGroup` | A chosen `Type v`. |
| `instValueGroup` | `LinearOrderedCommGroupWithZero F.ValueGroup`, for a bundle `F`. |
| `valuation` | `_root_.Valuation K F.ValueGroup`, using the stored ordered-group structure. |
| `instCompleteDiscrete` | `Valuation.IsCompleteDiscrete F.valuation`. |

`CompleteDVF.instValueGroup` and `CompleteDVF.instCompleteDiscrete` retain
their source instance attributes. Instance search can consequently recover
the ordered-group structure, the complete-discrete predicate, and its
rank-one discreteness field from a supplied bundle. The structure is
stand-alone; its constructor requires the displayed data and proofs.
The field universe `u` and value-group universe `v` remain independent.
The value group is freely chosen and is not required to be the whole
image of the valuation.

This unit defines the property and packages supplied data. It proves no
completeness, Henselianity, extension, or existence result. It supplies no
forgetful projections to `HenselianDVF` or `DVF`, no residue-data aliases,
no adic-completeness instance, and none of the source theorem rows.

## Exact source map and imports

Write `S = ValuationTheory.DiscreteValuationField` and
`T = Langlands.NYLL.ValuationTheory.DiscreteValuationField`.

| Original declaration | Adapted declaration and correspondence |
| --- | --- |
| `S.Valuation.IsCompleteDiscrete`, line 29, M107.001 | `T.Valuation.IsCompleteDiscrete`; both proof fields and their order are unchanged. |
| `S.Valuation.IsCompleteDiscrete.isRankOneDiscrete`, line 31 | `T.Valuation.IsCompleteDiscrete.isRankOneDiscrete`; instance attribute from line 36 retained. |
| `S.Valuation.IsCompleteDiscrete.isAdicComplete`, line 33 | `T.Valuation.IsCompleteDiscrete.isAdicComplete`; identical actual maximal ideal and valuation subring. |
| `S.CompleteDVF`, line 100, M107.006 | `T.CompleteDVF`; all four fields, their order, and independent universes are unchanged. |
| `S.CompleteDVF.ValueGroup`, line 102 | `T.CompleteDVF.ValueGroup`. |
| `S.CompleteDVF.instValueGroup`, line 104 | `T.CompleteDVF.instValueGroup`; instance attribute from line 110 retained. |
| `S.CompleteDVF.valuation`, line 106 | `T.CompleteDVF.valuation`. |
| `S.CompleteDVF.instCompleteDiscrete`, line 108 | `T.CompleteDVF.instCompleteDiscrete`; instance attribute from line 110 retained. |

Ordinary structure constructors, recursors, and generated projections belong
to these definitions. No original-namespace alias is introduced.

The extraction imports only
`Mathlib.RingTheory.Valuation.Discrete.Basic` and
`Mathlib.RingTheory.AdicCompletion.Basic`.
The first supplies `Valuation.IsRankOneDiscrete` and already imports
`Mathlib.RingTheory.Valuation.ValuationSubring`, supplying the actual
`valuationSubring` and its canonical local-ring structure.
The second supplies `IsAdicComplete`.
These replace the source imports of `DiscreteValuationField.Henselian`,
`DiscreteValuationField.AdicPower` and
`DiscreteValuationField.ValuationTransport`.
No NYLL theorem or bundle import is required by the two structural declarations.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this extraction.
The retained NOTICE contains no source-specific entry for the selected
`Valuation/DiscreteValuationField/Complete.lean`.

Worker 384 extracted the two structural declarations, added the
`Langlands.NYLL` namespace prefix, replaced the three source imports by
the two Mathlib imports above, removed the unused universe `w` and all
other declarations, and wrote this Markdown on 25 October 2026.
The Lean header prominently records the modifications. No compatibility
proof patch or implementation supplied by another project worker is used.
