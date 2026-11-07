# Nontriviality of the transported valuative relation

This module proves
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivial.{u}`.
Its complete type is the published proposition
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivialStatement.{u}`,
imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkNontrivialStatement`.
This is source unit M422.005.

## Exact scope

The universe `u` is arbitrary. The statement universally quantifies
`K : Type u`, followed by the supplied instances `Field K`,
`ValuativeRel K`, `TopologicalSpace K`, and
`IsNonarchimedeanLocalField K`, in that order. The proof introduces exactly
these binders. The statement includes these two local installations:

```lean
letI : Small.{0} K := nonarchimedeanLocalField_small K
letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
```

The first uses the published smallness theorem to form Mathlib's actual
universe-zero carrier `Shrink.{0} K`. The second uses the published relation,
which is `ValuativeRel.ofValuation (shrinkLocalFieldValuation K)`.
The proof body installs the same instances with anonymous `let` bindings,
as appropriate for a proposition-valued goal.
The field, relation and topology on `K` remain the supplied structures.
There is no extra smallness, equivalence or nontriviality premise, and this
module introduces no global instance. All imported Lean/Markdown pairs are
reused unchanged.

## Implemented proof

Write `v := shrinkLocalFieldValuation K`. By its published definition,

```text
v z = ValuativeRel.valuation K (Shrink.ringEquiv K z).
```

Thus `v` takes values in the original value group with zero of `K`. It is
compatible with the locally installed relation on `Shrink.{0} K`, by
`Valuation.Compatible.ofValuation v`.

The supplied local-field certificate gives `ValuativeRel.IsNontrivial K`.
Applying `ValuativeRel.isNontrivial_iff_isNontrivial` to the canonical
valuation of `K` gives its nontriviality as a valuation.
`Valuation.IsNontrivial.exists_val_nontrivial` supplies an element `x : K`
whose value is different from both zero and one.

Use `(Shrink.ringEquiv K).symm x` as the witness for `v`. Unfolding the
published pullback valuation and cancelling the ring equivalence with its
inverse identifies its value with `ValuativeRel.valuation K x`. The two
`simpa` steps in the proof transfer the inequalities with zero and one.
This proves `v.IsNontrivial`.

Finally, the reverse direction of
`ValuativeRel.isNontrivial_iff_isNontrivial v` proves
`ValuativeRel.IsNontrivial (Shrink.{0} K)` for the installed relation.
This class means that the value group with zero constructed from that
relation on `Shrink.{0} K` contains an element different from zero and one.
The criterion transfers nontriviality from the compatible valuation into
this value group; it does not identify it definitionally with the original
value group of `K`. Ordinary nontriviality of the field carrier would not
establish this conclusion.

## Original source and declaration map

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The full source file was read; its SHA-256 is
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
The section parameters occur at lines 27–28, the private smallness
wrapper at lines 30–31, and the selected theorem's signature and proof at
lines 56–71.

| Original declaration and unit | Adapted declaration |
| --- | --- |
| M422.005, `LocalFieldTheory.shrinkLocalField_isNontrivial` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivial` |
| Published universal target | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivialStatement` |

Worker 1686 isolated this proof in the focused `ShrinkNontrivialProof`
module and prefixed the namespace with `Langlands.NYLL`. The theorem's type
is the published universal target, so the four source section instances
are introduced in its body. The source's private `smallLocalField K`
wrapper is replaced by the published `nonarchimedeanLocalField_small K`.
The published valuation and relation are imported by Lean name instead of
being copied. The original anonymous `let` bindings are retained; the witness
argument, compatibility criterion and simplifications follow the original
proof. The original imports become the single exact-statement import.
Unused `Filter` and `Topology` openings and the enclosing `noncomputable
section` are omitted.

The source is registered in
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project, current Library or pinned-source `notes/errata`
directory was present at preparation. No feasibility draft or compatibility
patch is reused; M422 has no patch10 modification flag.

## Attribution and boundary

The Lean header preserves the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 attribution and authorship, including OpenAI Codex assistance.
Worker 1686 is the sole author of this new adaptation. The existing
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) match the pinned originals
byte for byte. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit proves only M422.005. M422.006–009 properties, coherent
Artin-family transport and host assembly remain separate obligations.
