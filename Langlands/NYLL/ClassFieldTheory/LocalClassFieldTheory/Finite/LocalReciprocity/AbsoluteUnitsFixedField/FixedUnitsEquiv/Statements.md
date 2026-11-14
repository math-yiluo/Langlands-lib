# Coercion target for the intermediate-field fixed-unit equivalence

The pinned original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`
(SHA-256 `392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public inventory `notes/reuse/nyll-public-port/m073-m096.md`, section M088,
records no patch10 modification of this source module. No applicable NYLL or
Yamaguchi erratum was found in the Library's `notes/errata/`.

## Exact source correspondence

| Unit and source lines | Original theorem | Public proposition definition |
| --- | --- | --- |
| M088.007; docstring 164, attribute 165, theorem 166–169, proof 170 | `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe` | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coeStatement` |

The complete parameter order is

```lean
(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
(E : IntermediateField K Ω) (x : Additive Eˣ)
```

The field parameters are explicit and universe zero. The source section
binders are at lines 33 and 55. There are no additional assumptions.

## Exact proposition and meaning

The `Prop` body is the source theorem's equality, unchanged:

```lean
(intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
  intermediateFieldUnitsToGaloisAmbient K Ω E x
```

It asserts that forgetting the fixedness proof from the canonical equivalence
returns the original inclusion of intermediate-field units into ambient units,
written additively. This file defines the proposition only. The source's
`rfl` proof is reserved for a separate proof task.

## Reuse and complete modification record

The only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions`.
It supplies M088.006 and transitively the published M088.001–.002, the actual
ambient-unit representation and inclusion. Those declarations are reused by
Lean name; no replacement coefficient groups or inclusion maps are introduced.
The paired definition documentation explains the Library/Mathlib comparison.

Worker 324 extracted only M088.007, prefixed the source namespace with
`Langlands.NYLL`, changed `theorem` to `def ... : Prop :=`, appended `Statement`
to the name, and removed `@[simp]` and the source proof. The original theorem
docstring is replaced by a proposition-specific docstring. The broad original
imports and whole-file module documentation are replaced by the focused
import and documentation above. Source section variables are combined without
changing their order or binder kinds; the noncomputable section is retained;
the unused `CyclicCohomology` opening is omitted. No statement-body change,
new hypothesis, instance or proof is introduced.

## Development check

Focused `lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
succeeded with no errors or warnings, diagnostic
`537015b4-f25c-494c-9a68-51eef6b6ec58`. Inspection explicitly reports
`statement_returns_prop: true` and an empty universe-parameter list.
This is development evidence only; independent review and publication are
separate requirements.

## Attribution and scope

The Lean file retains the original copyright and author header verbatim:
Copyright (c) 2026 Naganori Yamaguchi, all rights reserved; Authors: Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 attribution and notices remain
in the published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 324 extracted the unit and wrote this modification record on 14 November
2026. This support unit establishes no host class-formation, cup, transfer,
Tate or reciprocity target.
