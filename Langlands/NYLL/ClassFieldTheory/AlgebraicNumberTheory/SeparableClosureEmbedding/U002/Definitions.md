# A chosen embedding of a separable extension into the fixed separable closure

`Langlands.NYLL.AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure`
is the chosen `K`-algebra embedding of a separable field extension `L / K`
into Mathlib's fixed `SeparableClosure K`. Its complete telescope and body are:

```lean
universe u v

(K : Type u) (L : Type v)
[Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L] :
L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift
```

The universes `u` and `v` are independent, and `K` and `L` are explicit arguments.
The four instance arguments are retained in source order. The result is data,
a `K`-algebra homomorphism, whose underlying function is injective because its
domain is a field. The choice is noncomputable. The definition imposes no
finite-dimensionality, normality, topology, number-field or local-field
hypothesis and asserts no uniqueness or compatibility between choices.

## Source and attribution

This extracts precisely M001.002, original
`AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure`, from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean`,
lines 57–66 (section parameters at 59–60, declaration at 64–66).
The original file SHA-256 is
`40b9e61892ae3b770967cee9c5d95bd41c2d0357909af82ab0e38a8a527be77f`.
The complete source module, including its section context, was read and its
hash verified. No project or current Library `notes/errata` directory was
present on 10 November 2026.

The retained original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its source registration is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright and author header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`); Authors: Naganori Yamaguchi
(assisted by OpenAI Codex). The code remains under Apache-2.0, with the
retained license and notice at `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already present in the Library and verified
byte-identical to the pinned originals. Worker 169 performed this extraction and adaptation;
no other worker's draft or compatibility patch was reused.

## Canonical reuse and imports

The implementation reuses Mathlib's full-name construction `IsSepClosed.lift`,
defined in `Mathlib/FieldTheory/IsSepClosed.lean`. That construction chooses a
`K`-algebra homomorphism from a separable extension `L` into any separably closed
extension `M` of `K`. Here its target is specialized to Mathlib's
`SeparableClosure K`, using the canonical instance
`SeparableClosure.isSepClosed`. Both the closure abbreviation and this instance
are supplied by the same module. No new existence proof or global instance
is introduced.

Existing Library code in
`Langlands.FieldTheory.henselianSeparableAddValuation` also uses
`IsSepClosed.lift` internally, to construct a valuation on `L`; its output and
henselian valuation inputs differ from this embedding interface.
`Langlands.LocalGalois.Separable.fixedFieldToSepClosure` is instead the
inclusion of a particular intermediate field of a supplied local field's
separable closure. Neither construction replaces this source interface.
This unit directly reuses the general Mathlib construction.

The sole direct import is `Mathlib.FieldTheory.IsSepClosed`. This keeps the
implementation entirely within the approved Mathlib environment and removes
the original module's `Mathlib.FieldTheory.KrullTopology` and
`Mathlib.NumberTheory.NumberField.Basic` imports. The original continuity
theorem M001.001 and number-field specializations M001.003–006 do not occur in
this definition.

## Modification record and validation

The adaptation adds the `Langlands.NYLL` namespace prefix and extracts the
declaration into
`Langlands/NYLL/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding/U002/Definitions.lean`.
It preserves the source's `noncomputable section`, independent universe
parameters, explicit field parameters, all instance arguments, documentation
for the declaration, return type, and literal `IsSepClosed.lift` body.
It adds a module source note and this paired Markdown. No compatibility
change to the construction is needed.

Development checking uses environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). The entry module compiled with
zero errors and warnings using only the direct Mathlib import above.
Declaration inspection reports a definition with level parameters `u` and `v`,
a data-valued result, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. These development checks establish the
reduced import closure; independent semantic review and publication are
separate requirements. This unit supplies the chosen embedding only; it does
not discharge a reciprocity or class-formation target.
