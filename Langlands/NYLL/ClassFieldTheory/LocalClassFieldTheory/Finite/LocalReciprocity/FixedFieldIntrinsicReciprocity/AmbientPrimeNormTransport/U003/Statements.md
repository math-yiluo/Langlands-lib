# The chosen transported unit has valuation one: statements

This module defines two closed propositions:

- `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_sourceStatement : Prop`,
  the statement phase of source row M283.003, the theorem
  `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_source`;
- `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_targetStatement : Prop`,
  the statement phase of source row M283.004, the theorem
  `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_target`.

The module contains no proof. Separate proof children will prove them under
the names `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_source`
and `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_target`.

## Complete closed telescopes

Neither definition has parameters or universe variables. The body of
`chosenValuationOneUnitOfRingEquiv_sourceStatement` is

```lean
∀ (L M : Type)
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  (phi : L ≃+* M)
  (hmem : ∀ x : L,
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring),
  Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap L
      (Additive.ofMul
        (chosenValuationOneUnitOfRingEquiv L M phi hmem)) = 1
```

and the body of `chosenValuationOneUnitOfRingEquiv_targetStatement` is

```lean
∀ (L M : Type)
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  (phi : L ≃+* M)
  (hmem : ∀ x : L,
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring),
  Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
      (Additive.ofMul
        (Units.mapEquiv phi.toMulEquiv
          (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1
```

Both have the same eleven binders, in the source order:

| Binder | Kind and meaning |
| --- | --- |
| `L : Type`, `M : Type` | Explicit field types, in universe zero as in the source |
| `[Field L]`, `[ValuativeRel L]`, `[TopologicalSpace L]`, `[IsNonarchimedeanLocalField L]` | Instance-implicit structures making `L` a nonarchimedean local field |
| `[Field M]`, `[ValuativeRel M]`, `[TopologicalSpace M]`, `[IsNonarchimedeanLocalField M]` | The same four structures on `M` |
| `(phi : L ≃+* M)` | Explicit ring equivalence |
| `(hmem : …)` | Explicit hypothesis that `x` is an integer of `L` exactly when `phi x` is an integer of `M` |

Every binder is quantified inside the proposition. The hypothesis keeps its
source name `hmem` because both conclusions use it, as an argument of
`chosenValuationOneUnitOfRingEquiv`.

## Meaning

`chosenValuationOneUnitOfRingEquiv L M phi hmem : Lˣ` is the published
adaptation of M283.002. It is `Classical.choose` applied to the published
theorem `exists_valuationOne_unit_of_ringEquiv`, so it is one fixed witness
of the existence of a unit `p` of `L` with
`valuationMap L (Additive.ofMul p) = 1` and
`valuationMap M (Additive.ofMul (Units.mapEquiv phi.toMulEquiv p)) = 1`.

- The source statement says that this chosen unit has normalized valuation
  `1` in `L`.
- The target statement says that its image under `phi`, the unit
  `Units.mapEquiv phi.toMulEquiv (chosenValuationOneUnitOfRingEquiv L M phi hmem) : Mˣ`
  whose underlying element is `phi` of the chosen unit, has normalized
  valuation `1` in `M`.

`Additive.ofMul` only changes the type tag, so that a unit can be fed to the
additive homomorphism `valuationMap`.

`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K :
Additive Kˣ →+ ℤ` is the published adaptation of source row M134.002. It
sends a unit through the valuation of `K` and Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` of the value group
with `ℤᵐ⁰`, and reads off the integer. A uniformizer gets `-1`, so value `1`
belongs to inverses of uniformizers.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M283.002, `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv` | `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U002.Definitions` (the sole import) |
| M134.002, `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`, reached through the import |
| Mathlib `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.valuationSubring`, `Units.mapEquiv`, `RingEquiv.toMulEquiv` | Used unchanged, through the import's Mathlib closure |

The source opens `LocalFieldTheory` and writes
`IsNonarchimedeanLocalField.valuationMap`. The adaptation writes the full
published name.

## Library search

The whole Library at commit `451cce4ca176c34856be86a36801b7a3b585ae77` was
searched for `chosenValuationOneUnitOfRingEquiv` and for names containing
`valuationOne`. Neither source theorem nor any statement about a chosen
valuation-one unit occurs. So nothing in the Library already covers M283.003
or M283.004.

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
| M283.003, `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_source` | docstring 108, signature 109–121, proof 122–123 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_sourceStatement` |
| M283.004, `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_target` | docstring 125–126, signature 127–140, proof 141–142 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv_targetStatement` |

The source signatures are

```lean
theorem chosenValuationOneUnitOfRingEquiv_source
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul
          (chosenValuationOneUnitOfRingEquiv L M phi hmem)) = 1

theorem chosenValuationOneUnitOfRingEquiv_target
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul
          (Units.mapEquiv phi.toMulEquiv
            (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1
```

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted types directly from the pinned original on
13 November 2026 and made these changes:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. All eleven binders move inside the proposition in the same order,
  with the same binder kinds, the same name `hmem` and the source's
  universe-zero `Type`. The proofs are omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
- The valuation map is written by its full published name, and the `open`
  lines are omitted.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by the single published
  module that defines `chosenValuationOneUnitOfRingEquiv`.
- The `noncomputable section` and all other declarations of the source file
  are omitted. A proposition definition needs no noncomputable section.

The original docstrings are kept on the definitions. No instance or simp
attribute is installed. No shared draft or other worker's unpublished work
was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only these two statements. Their truth proofs belong to
separate proof units published after the statements are accepted, one per
statement. The theorem `valuationSubring_mem_iff_of_separableClosureRingEquiv`
(M283.005, lines 144 onward) and all later M283 rows are separate units.
