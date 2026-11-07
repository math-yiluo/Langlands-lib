# Strict comparison of canonical valuations on a local field and its Shrink

This module defines the universal proposition
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_valuation_lt_iffStatement.{u}`,
the statement phase of source row M422.006. It packages the complete source
theorem signature, including its section parameters, as a `def` returning
`Prop`. It supplies no proof of that proposition. The later exact proof
child will prove the published target with the name
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_valuation_lt_iff`.

## Parameters and local instances

The proposition universally quantifies the following parameters in order:

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The universe `u` is arbitrary, and all four instances are supplied. The
field, valuative relation and topology are those supplied on `K`, with its
supplied nonarchimedean-local-field certificate. The proposition then installs
exactly these two local instances:

```lean
letI : Small.{0} K := nonarchimedeanLocalField_small K
letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
```

Both names denote the published declarations in
`Langlands.NYLL.LocalFieldTheory`. The smallness theorem provides the proof
needed to form Mathlib's actual `Shrink.{0} K : Type 0`. The relation is the
published `ValuativeRel.ofValuation (shrinkLocalFieldValuation K)`, reused
by name. There is no additional `Small` parameter, chosen equivalence,
assumed comparison or restriction to a particular presentation of `K`.
The module introduces no global instance.

## Exact comparison and its value groups

After those local instance choices, the rest of the proposition is

```lean
∀ x y : Shrink.{0} K,
  ValuativeRel.valuation (Shrink.{0} K) x < ValuativeRel.valuation (Shrink.{0} K) y ↔
    ValuativeRel.valuation K (Shrink.ringEquiv K x) <
      ValuativeRel.valuation K (Shrink.ringEquiv K y)
```

The valuation on the left is Mathlib's canonical valuation

```lean
ValuativeRel.valuation (Shrink.{0} K) :
  Valuation (Shrink.{0} K) (ValuativeRel.ValueGroupWithZero (Shrink.{0} K))
```

for the locally installed transported relation. Its canonical value group
lies in universe zero. The valuation on the right is

```lean
ValuativeRel.valuation K : Valuation K (ValuativeRel.ValueGroupWithZero K)
```

for the supplied relation on `K`. Its value group lies in universe `u`.
The right side evaluates this valuation at the images under the actual
Mathlib equivalence `Shrink.ringEquiv K : Shrink.{0} K ≃+* K`.

Each strict inequality is internal to its own canonical value group. The
target relates the two inequalities by an equivalence of propositions; it
does not identify the value groups. In particular, its left valuation is
the canonical valuation on the small carrier. The imported data
`shrinkLocalFieldValuation K` instead takes values in
`ValuativeRel.ValueGroupWithZero K`; it defines the transported relation
but does not replace the left canonical valuation in this target.

The single import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuativeRel`.
Its dependencies already supply the smallness theorem, pulled-back
valuation and Mathlib's transported ring and field structures. Those
published Lean/Markdown pairs are reused unchanged. This comparison
requires no topology on the small carrier and imports no preceding
nontriviality proof.

## Original source and declaration map

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The complete file was read and its SHA-256 verified as
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
The section parameters occur at lines 27–28, the private smallness wrapper
at lines 30–31, and the transported relation at lines 42–46. The selected
docstring, signature and proof occupy lines 73–93; the theorem begins
at line 75.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M422.006, `LocalFieldTheory.shrinkLocalField_valuation_lt_iff` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_valuation_lt_iffStatement`, universal Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_valuation_lt_iff`, reserved for the exact proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project, current Library, literature or pinned-source
`notes/errata` directory existed at the preparation check.

## Adaptations and attribution

Worker 1686 isolated the signature of M422.006 in the focused
`ShrinkValuationLtStatement` module and prefixed the source namespace with
`Langlands.NYLL`. The section parameters become universal binders inside
the proposition, retaining their order and explicitness. The original
private `smallLocalField K` wrapper is replaced by local use of the
published `nonarchimedeanLocalField_small K`. The published transported
relation is installed locally by its existing name.

The original theorem becomes a Prop-valued definition with the
`Statement` suffix, and its proof is omitted for the separate proof phase.
The valuation name is fully qualified as `ValuativeRel.valuation`.
The original source imports are replaced by the single published relation
import and its dependencies. Unused `Filter` and `Topology` openings and
the enclosing `noncomputable section` are omitted. No compatibility patch
or private feasibility draft is reused.

The Lean header retains the original 2026 Naganori Yamaguchi copyright,
authorship including OpenAI Codex assistance, and Apache-2.0 attribution.
The existing [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) match the pinned upstream
files byte for byte. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The root NOTICE has no entry for the selected source module.

This unit contains only the M422.006 statement target. Its proof,
M422.007–009 properties, valuation-extension transport, Artin-family
transport and host assembly belong to separate units.
