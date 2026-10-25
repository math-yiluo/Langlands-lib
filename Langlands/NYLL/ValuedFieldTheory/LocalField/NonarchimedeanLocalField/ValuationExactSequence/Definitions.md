# Bundled normalized valuation maps on field units

This module extracts the two tightly coupled data definitions M134.001–002
from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 30–41](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L30-L41),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The main definition is
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`;
the multiplicative homomorphism immediately preceding it supplies its body.

Both definitions retain exactly the parameters
`(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, with arbitrary universe `u`. The last
typeclass is Mathlib's existing class. All constructions use the supplied
field, valuative relation and topology.

## Exact source correspondence

| Original declaration | Adapted declaration | Source unit and lines |
| --- | --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom` | M134.001, lines 31–36 |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | M134.002, lines 39–41 |

The two construction bodies are unchanged. No names or instances are
installed in the original global namespace.

## Construction and conventions

`valuationUnitsMulHom K : Kˣ →* Multiplicative Int` is the composition,
in order of application, of:

1. `Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom`,
   mapping field units to units of the actual `ValuativeRel.ValueGroupWithZero K`;
2. `Units.map
   (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom`,
   mapping these units to units of `WithZero (Multiplicative Int)` using
   Mathlib's actual order-preserving value-group isomorphism;
3. `(@WithZero.unitsWithZeroEquiv (Multiplicative Int) _).toMonoidHom`,
   extracting the nonzero multiplicative integer from such a unit.

`valuationMap K : Additive Kˣ →+ Int` is exactly
`MonoidHom.toAdditive (valuationUnitsMulHom K)`. This reinterprets the
multiplicative homomorphism as an additive one; the type tags identify
`Additive (Multiplicative Int)` with `Int`. The underlying function and
the source sign are retained, without applying a negation. The
homomorphism laws and required nonzero certificates come from these existing
Mathlib constructions. No new mathematical theorem is needed to build either
definition.

## Imports and scope

The only direct import is `Mathlib.NumberTheory.LocalField.Basic`, which
provides `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` and, through
its Mathlib import closure, the homomorphism, type-tag, unit and WithZero
support used in both bodies. No NYLL source module is imported.

The partition's incoming M130/M133 edges describe the source file's whole
imports. Neither retained body uses the source function `v` or any source
valuation theorem, so this extraction has no mathematical publication
dependency on M128.001. It does not import `Valuation.lean` or
`IdealQuotients.lean`.

This module contains only the two definitions. The source
`valuationShortComplex`, `valuationMap_apply`, surjectivity and uniformizer
results, integer-unit maps, quotient isomorphisms, sections and exact-sequence
development are outside its scope. It makes no equality claim with `v` or a
host `ord`, and proves no sign comparison, Artin-action normalization or
reciprocity statement. Those require their separately published statements
and proofs. In particular, the audit and partition notes describe a port
plan; they do not establish those later results for this extraction.

## Source record and attribution

The original source is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The selected original file has SHA256
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the project's published errata lookup.

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex). The source is released
under Apache-2.0. The existing, unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany the extraction
and match the pinned originals byte for byte. The selected source file is
absent from the root NOTICE's source-file inventory and the supplement's
ValuedFieldTheory third-party source table; all notices in the existing
NOTICE remain preserved.

Worker 449 independently extracted these two definitions from the pinned
original on 25 October 2026, prefixed the namespace with `Langlands.NYLL`,
replaced the source import list with the single Mathlib import, and wrote
this documentation. No private adaptation by another worker was reused.
The Lean header records these modifications. The original uses Lean
4.35.0-rc2 and a different Mathlib revision; this extraction targets the
project's approved Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
