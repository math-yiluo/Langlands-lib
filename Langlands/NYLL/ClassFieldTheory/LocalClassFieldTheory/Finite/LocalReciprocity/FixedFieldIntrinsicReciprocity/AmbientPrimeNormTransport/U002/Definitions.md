# A chosen valuation-one unit transported by a ring equivalence: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv`.
It is the adaptation of source row M283.002, the noncomputable definition
`LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv`. It fixes, by
choice, one unit of `L` that the published theorem
`exists_valuationOne_unit_of_ringEquiv` (M283.001) says exists.

## Declaration

```lean
noncomputable def chosenValuationOneUnitOfRingEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    Lˣ :=
  Classical.choose
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)
```

The parameters, in the source order, are:

| Parameter | Kind and meaning |
| --- | --- |
| `L : Type`, `M : Type` | Explicit field types, in universe zero as in the source |
| `[Field L]`, `[ValuativeRel L]`, `[TopologicalSpace L]`, `[IsNonarchimedeanLocalField L]` | Instance-implicit structures making `L` a nonarchimedean local field |
| `[Field M]`, `[ValuativeRel M]`, `[TopologicalSpace M]`, `[IsNonarchimedeanLocalField M]` | The same four structures on `M` |
| `(phi : L ≃+* M)` | Explicit ring equivalence |
| `(hmem : …)` | Explicit proof that `x` is an integer of `L` exactly when `phi x` is an integer of `M` |

The result is a unit of `L`. The definition is noncomputable because it uses
`Classical.choose`.

## Meaning

`IsNonarchimedeanLocalField` is Mathlib's root class: the topology is the
valuative one, the field is locally compact and the valuation is nontrivial.
`ValuativeRel.valuation L` is Mathlib's canonical valuation of the valuative
relation, and `.valuationSubring` is its ring of integers.

The published theorem
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`
has type `exists_valuationOne_unit_of_ringEquivStatement`. Applied to
`L M phi hmem`, it proves

```lean
∃ p : Lˣ,
  Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap L
      (Additive.ofMul p) = 1 ∧
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
      (Additive.ofMul (Units.mapEquiv phi.toMulEquiv p)) = 1
```

`Classical.choose` returns a witness of this existential. So the defined
unit has normalized valuation `1` in `L`, and its image under `phi` has
normalized valuation `1` in `M`. These two facts are the source theorems
M283.003 and M283.004. Their statements are in the separate module
`AmbientPrimeNormTransport/U003/Statements`. Nothing else about the chosen
unit is specified: it is one fixed but unspecified witness. In the sign
convention of the published `valuationMap`, a unit of value `1` is the
inverse of a uniformizer of `L`.

The value depends on the proof `hmem` only through its type. Lean's proof
irrelevance makes any two proofs of the same proposition definitionally
equal.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M283.001, `LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv` | `Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U001.Proofs` (the sole import) |
| Mathlib `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.valuationSubring`, `Classical.choose` | Used unchanged, through the import's Mathlib closure |

The source body applies the theorem `exists_valuationOne_unit_of_ringEquiv`
in the same namespace. The published proof keeps that name, so the body is
unchanged.

## Library search

The whole Library at commit `2e46b9cac0230529f50cdf96bbe4713c06701fc2` was
searched for `chosenValuationOneUnitOfRingEquiv`, for
`exists_valuationOne_unit_of_ringEquiv`, and for names containing
`valuationOne`. The M283.001 name occurs only in its published statement
and proof modules (`AmbientPrimeNormTransport/U001/Statements` and
`AmbientPrimeNormTransport/U001/Proofs`); the only other `valuationOne`-like
match is the unrelated
`evaluationOne` in `Langlands/Weil/Representation/InductionSemisimplicityProof.lean`.
No declaration chooses a valuation-one unit compatible with a ring
equivalence. So nothing in the Library already covers M283.002.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean>).
The complete file was read; its SHA-256 is
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`.
The header is at lines 1–5, the imports at 7–8, the module docstring at
10–16, `noncomputable section` at 20, the namespace at 22 and the `open`
lines at 24–26.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M283.002, `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv` | docstring 92–93, signature 94–104, body 105–106 | `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the definition directly from the pinned original on
13 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
- The telescope, the docstring, the `noncomputable` modifier and the body
  are kept unchanged.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by the single published
  module that proves `exists_valuationOne_unit_of_ringEquiv`.
- The `open` lines are omitted, because the declaration uses no name from
  the opened namespaces. A local `noncomputable section` wraps the
  definition, as in the source.
- All other declarations of the source file are omitted.

No instance, simp or other attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this definition. The theorems
`chosenValuationOneUnitOfRingEquiv_source` (M283.003) and
`chosenValuationOneUnitOfRingEquiv_target` (M283.004), and all later M283
rows, are separate units.
