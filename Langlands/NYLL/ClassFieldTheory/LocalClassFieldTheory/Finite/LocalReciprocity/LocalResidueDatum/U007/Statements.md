# Pullback of the chosen separable valuation ring: target

This module states NYLL source unit M249.007 as a closed proposition. It
exports one Prop-valued definition,
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullbackStatement`.
Nothing is proved here; the proof is a separate unit under the adapted source
name `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullback`.

Mathematically, the target says: for a nonarchimedean local field `K`, an
element `x` of `K` lies in the chosen valuation ring of the separable closure
exactly when it lies in the valuation ring of the canonical discrete
valuation of `K`. So the chosen valuation ring of `SeparableClosure K` lies
over the valuation ring of `K`: it defines a place `w | v` above the place `v`
of `K`. In the source, this is the input from which the instance M249.008
(`localSeparableValuationHasExtension`) shows that the valuation of the chosen
ring extends the valuation of `K`.

## The proposition

```lean
def localSeparableValuationSubring_pullbackStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K),
    algebraMap K (SeparableClosure K) x ∈
        localSeparableValuationSubring K ↔
      x ∈ (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation.valuationSubring
```

There is no level parameter: `K` lives in `Type`, as in the source. The
quantified binders, in order, are the section variables of the source (lines
45–46) followed by the explicit parameter of the source theorem:

| Binder | Meaning |
| --- | --- |
| `K : Type` | the base field |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| `x : K` | an element of `K` |

The left side of the equivalence is membership of the image of `x` under
Mathlib's algebra map `K → SeparableClosure K` in the chosen valuation
subring. The right side is membership of `x` in the valuation subring
(Mathlib's `Valuation.valuationSubring`) of the canonical valuation of `K`.

### Published declarations used

- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K`
  (M249.006, [definition](../U006/Definitions.md)): the preimage, under the
  inclusion `SeparableClosure K → AlgebraicClosure K`, of a valuation subring
  of `AlgebraicClosure K` chosen by Chevalley's extension theorem.
- `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` (M248.001,
  [the canonical complete DVF](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/Canonical.md)):
  the canonical valuation of `K` packaged as a complete discrete valuation
  field; `.valuation` is that valuation. It is used at universe `0`.

The statement needs neither of the local instances M249.001 and M249.002:
`algebraMap K (SeparableClosure K)` is Mathlib's algebra structure of the
intermediate field over `K`.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the declaration reported kind
`definition`, no level parameters, `statement_returns_prop: true`, and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports and scope

The only import is the published module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`.
It supplies `localSeparableValuationSubring` and, through its imports,
`localCompleteDVF`, Mathlib's `IsNonarchimedeanLocalField`, `SeparableClosure`
and `Valuation.valuationSubring`.

Only M249.007 is stated. The private source lemma M249.004 used in its source
proof is not stated here; the separate proof unit need not use it.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L94-L104)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the
value recorded for M249 in the
[public declaration partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).

| Partition unit | Original theorem in `LocalClassFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M249.007 | `localSeparableValuationSubring_pullback` | 94–104 | `localSeparableValuationSubring_pullbackStatement` |

Line 94 is the doc comment, line 95 the theorem name with its parameter
`(x : K)`, lines 96–98 the conclusion, and lines 99–104 the source proof. The
source module opens namespace `LocalClassFieldTheory` (line 31), opens
`LocalFieldTheory` (line 35), works in `noncomputable section` (line 39) and
declares the section variables at lines 45–46.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` prefix to the namespace. The chosen ring is the
  published prefixed definition of the same name. The source spells the
  canonical valuation `localCompleteDVF K`, relying on the opened namespace
  `LocalFieldTheory`; the adapted statement spells out the published name
  `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`;
- packaged the theorem type as the closed proposition above. The section
  variables become the leading `∀`-binders and the source parameter `x`
  follows, with the same kinds (explicit for `K` and `x`, instance-implicit
  for the rest);
- omitted the source proof and the source's `open` lines, which the statement
  does not need;
- replaced the source imports by the published module above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `LocalResidueDatum.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
