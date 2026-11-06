# The valuative relation on the universe-zero Shrink carrier

This module defines the data
`Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuativeRel.{u}`,
corresponding to source unit M422.003. It applies Mathlib's existing
`ValuativeRel.ofValuation` constructor to the published
`Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuation`.

## Complete parameters and local smallness

The parameters, in order and with their original explicitness, are

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The universe `u` is arbitrary. The definition uses the supplied field,
valuative relation and topology. Both the type and body install

```lean
letI : Small.{0} K := nonarchimedeanLocalField_small K
```

where the theorem is the published
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small`.
There is no extra `Small` parameter or chosen equivalence. This local proof
allows formation of Mathlib's actual `Shrink.{0} K : Type 0`.

With that local instance the type is

```lean
ValuativeRel (Shrink.{0} K)
```

and the value is

```lean
ValuativeRel.ofValuation (shrinkLocalFieldValuation K)
```

The single import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuation`.
It supplies the smallness theorem and Mathlib's transported ring and field
structures. These are the same structures used by the accepted valuation;
the ring underlying the transported field agrees with the transported ring
by reduction. No new ring or field structure is constructed.

The definition keeps the source's `@[instance_reducible]` attribute and is
explicitly `noncomputable`. It provides relation data for local installation
as a typeclass instance. It declares no global instance on `Shrink.{0} K`.

## Defining relation

After locally installing the smallness proof above and

```lean
letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
```

the proposition `x ≤ᵥ y`, for `x y : Shrink.{0} K`, reduces to

```lean
ValuativeRel.valuation K (Shrink.ringEquiv K x) ≤
  ValuativeRel.valuation K (Shrink.ringEquiv K y)
```

Indeed, Mathlib's `ValuativeRel.ofValuation` defines its `vle` field by
`vle x y := v x ≤ v y`. The imported valuation is
`(ValuativeRel.valuation K).comap (Shrink.ringEquiv K).toRingHom`,
and Mathlib's `Valuation.comap` evaluates by composition.
Thus the displayed description follows by unfolding the two data
definitions and Mathlib's constructors. No separate substantive property
theorem is needed or supplied.

## Original source and exact declaration map

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The complete file was read and its SHA-256 verified as
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
The section parameters occur at lines 25–27, the private smallness wrapper
at lines 29–31, the valuation at lines 34–38, and this relation definition
at lines 42–46.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M422.003, `LocalFieldTheory.shrinkLocalFieldValuativeRel` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuativeRel` |

The source collection is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No project, current Library or literature `notes/errata` directory existed
when this unit was prepared.

## Modifications and attribution

Worker 1686 isolated M422.003 in the focused `ShrinkValuativeRel` module,
prefixed the source namespace with `Langlands.NYLL`, and replaced the section
variables with explicit declaration binders in the same order. The private
`smallLocalField K` wrapper becomes local use of the accepted theorem
`nonarchimedeanLocalField_small K` in both type and body. The accepted
valuation is imported instead of copying M422.002. The original `by` body
is written in term mode; the constructor and its argument are unchanged.
The source's unused `Filter` and `Topology` openings and enclosing
`noncomputable section` are omitted; the declaration itself remains explicitly
`noncomputable`. The source imports are replaced by the one published
valuation import and its existing dependencies.

The Lean header preserves the original 2026 Naganori Yamaguchi copyright,
authorship including OpenAI Codex assistance, and Apache-2.0 attribution.
The existing [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) match the pinned upstream files
byte for byte. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No feasibility draft or compatibility patch is reused.

## Scope

This unit supplies only M422.003 relation data. M422.001 is resolved by reuse
of the accepted smallness theorem and M422.002 by importing the accepted
valuation. This unit contains no M422.004–009 property, transported topology,
local-field proof, valuation-extension transport, coherent Artin-family
transport or host assembly.
