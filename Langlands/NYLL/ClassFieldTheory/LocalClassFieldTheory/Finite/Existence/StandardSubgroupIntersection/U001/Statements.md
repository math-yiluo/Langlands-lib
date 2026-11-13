# Intersecting standard norm conditions: proposition target

This module defines the universe-polymorphic closed proposition
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement.{u}`.
With `open scoped ValuativeRel`, `open LocalFieldTheory` and
`open LocalFieldTheory.IsNonarchimedeanLocalField` inside
`namespace Langlands.NYLL.LocalClassFieldTheory`, its exact body is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (ϖ : Kˣ) (d n : Nat)
  (_hϖ : valuationMap K (Additive.ofMul ϖ) = 1),
  unramifiedNormSubgroup K d ⊓
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n ≤
    LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n
```

It says: let `K` be a nonarchimedean local field (a field with a valuation
relation and a topology satisfying Mathlib's `IsNonarchimedeanLocalField`) in
an arbitrary universe `u`, let `ϖ ∈ Kˣ` have normalized valuation `1`, and let
`d` and `n` be natural numbers. Then every unit whose normalized valuation is
divisible by `d` and which lies in `⟨ϖ⟩ · Uⁿ` already lies in `⟨ϖ^d⟩ · Uⁿ`.

The objects are the actual published ones:

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K`
  is the normalized valuation `Additive Kˣ →+ Int` (published unit M134.002);
  the hypothesis is the equation `valuationMap K (Additive.ofMul ϖ) = (1 : Int)`.
- `Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup K d` is the
  subgroup of units whose normalized valuation is divisible by `(d : Int)`
  (published unit M266.011).
- `Langlands.NYLL.LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ e n` is
  `Subgroup.zpowers (ϖ ^ e) ⊔ fieldPrincipalUnits K n` (published unit
  M289.002); it is used with `e = 1` on the left and `e = d` on the right.
- `⊓` and `≤` are the meet and order of `Subgroup Kˣ`.

The universe `u` is retained as the declaration's single level parameter, and
`d` and `n` range over all natural numbers, zero included, as in the source.
The only hypothesis on `ϖ` is the valuation-one equation of the source. This
is a proposition definition; no proof is asserted.

## Source and changes

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean#L37-L44),
lines 37–44: the theorem
`LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le`,
with its docstring at lines 35–36. This is unit M403.001 of the published
[NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md).
The full source file was read; its SHA-256 is
`6a1c34851b46b17075888f452875eb49d31dcb167147dfde1eb2e3acc8cb99b1`.
The enclosing `noncomputable section`, `namespace LocalClassFieldTheory`,
`open scoped ValuativeRel`, `open LocalFieldTheory`,
`open LocalFieldTheory.IsNonarchimedeanLocalField` and `universe u`
(lines 25–33) were read with the command; the file declares no `variable`
before line 37, so the displayed binders are the complete telescope. In the
source, `valuationMap` resolves to
`LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` and
`unramifiedNormSubgroup` to `LocalClassFieldTheory.unramifiedNormSubgroup`.

| Source | Adapted |
| --- | --- |
| theorem `LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le` | Prop definition `Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | published `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` |
| `LocalClassFieldTheory.unramifiedNormSubgroup` | published `Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup` |
| `LocalFieldTheory.uniformizerPrincipalSubgroup` | published `Langlands.NYLL.LocalFieldTheory.uniformizerPrincipalSubgroup` |
| `(d n : ℕ)` | `(d n : Nat)` |
| hypothesis name `hϖ` | `_hϖ` |
| `universe u` declared in the section | explicit level parameter `.{u}` on the definition |

Worker 346 made these modifications: the theorem's type is extracted and its
complete source telescope (binder kinds, instance order, explicit `ϖ`, `d`,
`n` and the hypothesis) is universally closed as a `def ... : Prop` with
explicit universe parameter `u`; the name is prefixed with `Langlands.NYLL`
and receives the `Statement` suffix; `ℕ` is spelled `Nat`; and the hypothesis
binder `hϖ` is renamed `_hϖ`, because in a proposition the hypothesis is not
referenced and the unused-variable linter otherwise warns. Binder names do not
affect the proposition. The conclusion and the hypotheses are otherwise
unchanged, and the source docstring is kept. The source proof (lines 45
onward) is omitted and remains a separate obligation. The source imports are
replaced by the published `UnramifiedNormSubgroup.U011.Definitions` (which
imports the published valuation map definitions) and
`StandardOpenSubgroups.UniformizerPrincipalSubgroup`; the target needs no
abstract class-field-theory, norm-topology or finite abelian subextension
modules.

The source was read from the retained snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable source erratum was found in the Library's errata notes.

The original copyright and author header is retained. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) in the Library are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's draft was reused, and no local, scoped or global instance is
introduced.

## Development checks

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), check
`a147a879-98a9-401a-b002-98f952ad4272` compiled the module with no errors or
warnings and inspected the declaration as a definition with
`statement_returns_prop: true` and exactly the level parameter `u`. A private
diagnostic, check `c415be20-605c-4a17-bc55-e8ab593055c8`, printed the
declaration with full names and universes and confirmed by `rfl`, at an
arbitrary universe, that it equals the displayed telescope written with fully
qualified names; it also instantiated the declaration at universe `1`. The
diagnostic is not part of this contribution. Independent semantic acceptance
and the proof are separate obligations.
