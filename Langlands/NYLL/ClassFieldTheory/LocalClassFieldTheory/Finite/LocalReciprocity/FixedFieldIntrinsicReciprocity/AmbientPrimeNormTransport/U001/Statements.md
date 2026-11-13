# Valuation-one units under valuation-compatible ring equivalences: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquivStatement : Prop`.
It is the statement phase of source row M283.001, the theorem
`LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`. The module
contains no proof. A later proof child will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv`.

## Complete closed telescope

The definition has no parameters and no universe variables. Its entire body is

```lean
∀ (L M : Type)
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  (phi : L ≃+* M),
  (∀ x : L,
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring) →
  ∃ p : Lˣ,
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul p) = 1 ∧
      Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul
          (Units.mapEquiv phi.toMulEquiv p)) = 1
```

The binders, in the source order, are:

| Binder | Kind and meaning |
| --- | --- |
| `L : Type`, `M : Type` | Explicit field types, in universe zero as in the source |
| `[Field L]`, `[ValuativeRel L]`, `[TopologicalSpace L]` | Instance-implicit field, valuative relation and topology on `L` |
| `[IsNonarchimedeanLocalField L]` | Instance-implicit: `L` is a nonarchimedean local field for these structures |
| `[Field M]`, `[ValuativeRel M]`, `[TopologicalSpace M]`, `[IsNonarchimedeanLocalField M]` | The same four structures on `M` |
| `(phi : L ≃+* M)` | Explicit ring equivalence |
| anonymous premise | The source hypothesis `hmem`, with the same type |

Every binder is quantified inside the proposition. The conclusion does not
mention the hypothesis, so its name `hmem` is dropped and the hypothesis
becomes an anonymous premise `… → …`. Its type is unchanged.

## Meaning

`IsNonarchimedeanLocalField` is Mathlib's root class from
`Mathlib/NumberTheory/LocalField/Basic.lean`. It extends
`IsValuativeTopology K`, `LocallyCompactSpace K` and
`ValuativeRel.IsNontrivial K`: the topology is the one defined by the
valuative relation, the field is locally compact, and the valuation is
nontrivial. `ValuativeRel.valuation L` is Mathlib's canonical valuation of
the valuative relation, and `.valuationSubring` is its valuation ring, the
ring of integers of `L`.

The premise says that, for every `x : L`, `x` is an integer of `L` exactly
when `phi x` is an integer of `M`. So `phi` and its inverse preserve the
rings of integers. Nothing else ties `phi` to the two valuative relations or
topologies; in particular there is no continuity premise.

The conclusion asserts that some unit `p` of `L` has normalized valuation
`1` in `L`, and that its image under `phi` also has normalized valuation `1`
in `M`. Here `Units.mapEquiv phi.toMulEquiv p : Mˣ` is the unit of `M` whose
underlying element is `phi p`. `Additive.ofMul` only changes the type tag, so
that the unit can be fed to the additive homomorphism `valuationMap`.

`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K :
Additive Kˣ →+ ℤ` is the published adaptation of source row M134.002. It
sends a unit through the actual valuation into
`ValuativeRel.ValueGroupWithZero K`, then through Mathlib's order-preserving
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰`, and reads off the integer. The source sign is kept unchanged, with
no negation. A nonzero element of the maximal ideal has valuation `< 1`, so
it gets a negative integer. Hence value `1` is attained by inverses of
uniformizers, not by uniformizers. This matches the source proof (lines
46–90), which takes `p` to be the inverse of a chosen uniformizer of `L`.
That explains the sign convention only. The statement asserts just the two
displayed equations.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M134.002, `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`, module `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions` (the sole import) |
| Mathlib `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.valuationSubring`, `Units.mapEquiv`, `RingEquiv.toMulEquiv` | Used unchanged, through the import's Mathlib closure |

The source opens `LocalFieldTheory` and writes
`IsNonarchimedeanLocalField.valuationMap`. The adaptation writes the full
published name. The class `IsNonarchimedeanLocalField` is Mathlib's root
class in both places.

## Library search

The whole Library at commit `8cfcc2bff12a9cb7a1f89a973a0c59f2dc39865a`
(whose Lean files are identical to those of the current base
`125eb56832ba1e00c87d0a67981fe249453d68b4`) was
searched for the published `valuationMap` and for ring equivalences
involving valuation subrings, uniformizers or valuation-one units. The NYLL
`valuationMap` occurs in the NYLL modules `ValuationExactSequence`,
`UnitTopology/U001`, `Basic`, `Basic/U016`, `NormContinuity/U003` and
`TopologicalReciprocity/U002`, and in the host files
`Langlands/ClassFieldTheory/Local/NYLL/SuppliedValuationSignStatement.lean`,
`SuppliedUnramifiedStatement.lean` and
`Langlands/Representation/Plancherel/LocalFieldUnits.lean`. None of them
states that a ring equivalence carries some unit of valuation one to a unit
of valuation one. The valuation-subring ring equivalences elsewhere in the
Library are constructions, not this statement. For example,
`Langlands/NYLL/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups/ValuationSubringAut.lean`
builds the automorphism of a valuation ring induced by a Galois element. So
nothing in the Library already covers M283.001.

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
| M283.001, `LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquiv` | docstring 28–29, signature 30–45, proof 46–90 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.exists_valuationOne_unit_of_ringEquivStatement` |

The source signature is

```lean
theorem exists_valuationOne_unit_of_ringEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    ∃ p : Lˣ,
      IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 ∧
        IsNonarchimedeanLocalField.valuationMap M
          (Additive.ofMul
            (Units.mapEquiv phi.toMulEquiv p)) = 1
```

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
13 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  All eleven binders move inside the proposition in the same order, with the
  same binder kinds and the source's universe-zero `Type`. The proof is
  omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
- The named hypothesis `hmem` becomes an anonymous premise of the same type.
- The valuation map is written by its full published name, and the `open`
  lines are omitted.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by the single published
  module that defines `valuationMap`.
- The `noncomputable section` and all other declarations of the source file
  are omitted. A proposition definition needs no noncomputable section.

The original docstring is kept on the definition. No instance or simp
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

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after this statement is accepted. The source
definition `chosenValuationOneUnitOfRingEquiv` (M283.002, lines 92 onward),
which chooses such a unit, and all later M283 rows are separate units.
