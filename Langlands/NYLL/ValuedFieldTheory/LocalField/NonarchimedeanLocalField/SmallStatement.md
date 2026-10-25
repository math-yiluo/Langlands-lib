# Universe-zero smallness of nonarchimedean local fields

`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_smallStatement.{u}`
is the universal proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K], Small.{0} K
```

The carrier universe `u` is arbitrary. All four structures are quantified
inside the proposition, in the source order. The conclusion uses Mathlib's
`Small` class at target universe zero: there exists a type `S : Type 0` and
a nonempty type of equivalences `K ≃ S`. It makes no countability assertion.
The supplied valuative relation and topology are retained throughout.
There is no smallness, finite-dimensionality, characteristic-zero, chosen-model,
extra completeness or proof-certificate premise.

This module defines a statement target. It provides neither a proof of that
target nor a `Small K` instance, a chosen shrinking equivalence, or transported
field, valuation or topology data.

## Source and adaptation

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean`.
The original theorem is `LocalFieldTheory.nonarchimedeanLocalField_small`,
lines 30–55, identified as M421.001 in the published declaration inventory.
Its signature is at lines 30–32 and its proof at lines 33–55.
The complete source file was read and its SHA-256 verified as
`5525b29447cab84c7c263ac5d7807911095bc4790c883b0be0f75fa845e3de27`.

The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is
[Small.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Small.lean>).
No project `notes/errata` directory was present at preparation; this is a
scoped project lookup, not an exhaustive external errata search.

The original-to-adapted map is:

| Original | Adaptation |
| --- | --- |
| `LocalFieldTheory.nonarchimedeanLocalField_small` | `Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_smallStatement` |
| Theorem signature, lines 30–32 | Full universal body of a `def : Prop`, preserving `u`, binder order, supplied structures and `Small.{0} K` |
| NYLL imports for `FiniteExtensionCompleteDVF` and `PrincipalUnits.Core` | Replaced for this statement by `Mathlib.NumberTheory.LocalField.Basic` |
| `Mathlib.Logic.Small.Basic` | Retained |
| Proof, lines 33–55 | Omitted |
| `noncomputable section` and namespace openings used by the proof | Omitted |

This adaptation was written directly from the pinned original. It reuses no
feasibility draft, patch10 adaptation or proof.

## Imports, reuse search and future proof boundary

The only imports are `Mathlib.NumberTheory.LocalField.Basic` and
`Mathlib.Logic.Small.Basic`. They provide every definition in the target.
The local-field class encodes compatibility of the supplied topology with the
valuative relation, local compactness and nontriviality. No NYLL
`localCompleteDVF` construction or source proof dependency is needed to state
the target.

At preparation, exact-name and smallness searches of the current Library,
Mathlib's local-field and valued-topology sources, and relevant active tasks
found no equivalent ready statement or theorem. Mathlib's general `Small`
interfaces, including `small_of_injective` and `small_of_surjective`, do not
by themselves establish the local-field target. This records the scoped search
outcome, not a claim that no alternative proof exists.

The original proof first injects the ring of integers into the function type
of sequences of its finite quotients by powers of the maximal ideal. That
sequence type is small in universe zero; an infinite product of finite types
need not be countable. It then uses the fraction-ring presentation to obtain
a surjection from pairs of integer-ring elements onto `K`, sending `(a, b)` to
`a / b`. These steps explain the source's smallness conclusion without claiming
countability of `K`. They describe the source proof only; no implementation or
proof acceptance is supplied here.

A later proof must prove this exact published proposition separately. Smallness
alone supplies no coherent family of transported local fields, Artin maps,
host reciprocity laws, cohomological comparisons or Weil systems.

## Attribution

The original copyright and authorship header is preserved in the Lean file,
with Worker 450's namespace, import and statement modifications recorded.
The existing Apache-2.0 [LICENSE](../../../../../licenses/NYLL/LICENSE) and
full [NOTICE](../../../../../licenses/NYLL/NOTICE) were verified byte for byte
against the pinned originals and are reused without duplication. Their
SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The selected source path is absent from the root NOTICE inventory and all five
`ANTHROPIC_FLT_SOURCE.md` inventories in the registered
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No third-party source listed in those inventories is copied into this unit.
