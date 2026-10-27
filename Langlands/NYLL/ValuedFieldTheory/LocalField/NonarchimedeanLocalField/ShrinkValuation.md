# The valuation on the universe-zero Shrink carrier of a local field

This module defines one piece of data,
`Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuation.{u}`. It is the
canonical valuation of a nonarchimedean local field `K`, pulled back to
Mathlib's universe-zero representative `Shrink.{0} K`.

## Parameters

The definition takes exactly the following parameters, in this order:

```text
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The carrier universe `u` is arbitrary. The field, valuative relation and
topology are the supplied ones. There is no `Small` premise, chosen
equivalence or substitute valuation among the parameters.

## Local smallness

Both the type and the body install

```lean
letI : Small.{0} K := nonarchimedeanLocalField_small K
```

using the published theorem
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small`. Its type
is the published universal proposition
`nonarchimedeanLocalField_smallStatement.{u}`, applied to `K` and the four
supplied instances. `letI` inlines this proof, so the elaborated type
mentions `Shrink.{0} K` with that smallness proof. No global `Small`
instance is declared. `Small.{0} K` is a proposition, so by proof
irrelevance `Shrink.{0} K` formed with any other smallness proof is the same
type definitionally.

## Type and value

With this smallness proof, the type is

```lean
Valuation (Shrink.{0} K) (ValuativeRel.ValueGroupWithZero K)
```

and the value is

```lean
(ValuativeRel.valuation K).comap (Shrink.ringEquiv K).toRingHom
```

Here `ValuativeRel.valuation K : Valuation K (ValueGroupWithZero K)` is
Mathlib's canonical valuation of the supplied valuative relation.
`Shrink.ringEquiv K : Shrink.{0} K ≃+* K` is Mathlib's ring equivalence; it
points from the small carrier to `K`. `Valuation.comap` pulls the valuation
back along the underlying ring homomorphism. The codomain is the original
value group `ValueGroupWithZero K`, which lies in universe `u`; it is not
moved to universe zero.

The ring structure on `Shrink.{0} K` in the type is found by instance
search. It is Mathlib's transported `Shrink.instRing`, and the ring
equivalence uses the matching transported addition and multiplication.
Mathlib's transported field structure on `Shrink.{0} K` comes from the
imported `Mathlib.Algebra.Field.Shrink`; its underlying ring agrees with
`Shrink.instRing` by unfolding reducible definitions and instances. A
private scratch check confirmed this with `with_reducible_and_instances rfl`.
No ring or field structure is constructed here.

## Defining evaluation

Unfolding `Valuation.comap` gives, for every `x : Shrink.{0} K`,

```text
shrinkLocalFieldValuation K x = ValuativeRel.valuation K (Shrink.ringEquiv K x).
```

This holds by `rfl`, and also by Mathlib's `Valuation.comap_apply`. A
private scratch check confirmed both. The module states no separate lemma
for it. There is no separate existence or equivalence theorem: the
definition is a data alias for this pullback.

## Original source and declaration map

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
Its SHA-256 is
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`. The
whole file was read. The section parameters are at lines 25–27, the private
smallness wrapper at lines 29–31, and the definition at lines 34–38.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M422.002, `LocalFieldTheory.shrinkLocalFieldValuation`, lines 34–38 | `Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuation` |
| M422.001, private `LocalFieldTheory.smallLocalField`, lines 29–31 | not ported; uses of it become uses of the published `Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The
associated supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. Its
publication manifest records the same SHA-256 for the source file. Neither
the current Library nor the project had a `notes/errata` directory when
this unit was prepared; this records the project lookup only.

## Changes from the original

- The namespace `LocalFieldTheory` becomes `Langlands.NYLL.LocalFieldTheory`.
- The section `variable` line becomes explicit binders on the definition, in
  the same order and with the same explicitness.
- The private wrapper `smallLocalField K` is not duplicated. Both
  `letI` occurrences use the published theorem
  `nonarchimedeanLocalField_small K` directly. In the original, the wrapper
  only restated NYLL's own `nonarchimedeanLocalField_small K`; the published
  Library theorem proves the same smallness for every such `K`.
- The original body `by letI ...; exact ...` becomes the same term written
  in term mode. The scoped openings `Filter` and `Topology` and the
  `noncomputable section` are omitted; the definition is marked
  `noncomputable` itself.
- The NYLL import `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Small`
  is replaced by the published Library module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SmallProof`.
  `Mathlib.Algebra.Field.Shrink` is kept.
  `Mathlib.Topology.Instances.Shrink` is dropped because this unit uses no
  topology on the small carrier. `Mathlib.Algebra.Ring.Shrink`, which
  defines `Shrink.ringEquiv`, is imported explicitly.

The type and value are otherwise unchanged.

## Scope

This module supplies valuation data only. It does not define the transported
valuative relation (M422.003). It states none of the properties M422.004–009:
local compactness, nontriviality, the valuation comparison, the topological
group and valuative topology properties, or that `Shrink.{0} K` is a
nonarchimedean local field. It gives no further transport results, coherent
Artin-family transport or host assembly.

## Attribution

The Lean file keeps the original 2026 Naganori Yamaguchi copyright and
authorship, including assistance by OpenAI Codex. It records Worker 231's
namespace, binder, smallness-wrapper and import changes. The existing
Apache-2.0 [LICENSE](../../../../../licenses/NYLL/LICENSE) and full
[NOTICE](../../../../../licenses/NYLL/NOTICE) are byte-for-byte copies of
the pinned upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
selected source file is not listed in the root NOTICE inventory or in the
supplement's `ANTHROPIC_FLT_SOURCE.md` inventories, so no third-party source
from those inventories is copied here. No feasibility draft or Worker 25
adaptation is reused.
