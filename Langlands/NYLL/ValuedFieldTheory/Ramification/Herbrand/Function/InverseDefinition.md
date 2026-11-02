# The inverse Herbrand function as data

This module adapts exactly M303.029 from Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`, lines 351–353](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L351-L353).
The complete original file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
The original imports, ambient telescope and local instances at lines 1–60,
and lines 340–489 containing the inverse and its surrounding laws, were
read directly for this extraction.

## Complete interface and defining expression

The declaration lies in
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
Within that namespace its full interface and body are:

```lean
noncomputable def inverseHerbrandFunction
    {G : Type u} [Group G]
    (F : AntitoneNormalSubgroupFiltration G) (t : ℝ) : ℝ :=
  Function.invFun (herbrandFunction F) t
```

The universe `u` is arbitrary. `G` is implicit, `Group G` is supplied,
and `F` and `t` are explicit. There are no further parameters, including
no `Finite G` or `Fintype G`. The forward function is the published
[`herbrandFunction`](Definitions.md): the shifted-cardinality,
natural-floor affine function, equal to the identity on negative reals.
Its source and paired documentation are reused unchanged.

Mathlib's `Function.invFun` chooses a preimage when one exists and an
arbitrary element of its nonempty domain otherwise. Here the domain
is `ℝ`, whose nonemptiness is supplied by the existing Mathlib instance.
It requires neither injectivity nor surjectivity to define this data.
Thus the name “inverse” specifies the chosen construction; this
declaration alone asserts no inverse equation for an arbitrary group
and filtration. The finite-group analytic results and the inverse laws
are separate results with their own hypotheses. An eventual-triviality
condition is not added.

## Exact source map and extraction

| Unit and original declaration | Adapted declaration |
| --- | --- |
| M303.029, `RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction` | `Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction` |

The namespace gains `Langlands.NYLL`. The individual docstring and
definition body are unchanged. The module imports the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions`
and explicitly imports `Mathlib.Logic.Function.Basic` for `Function.invFun`.
The original arithmetic, cardinality, floor and topology imports are
replaced by these focused imports; the required forward-function
prerequisites arrive through its published module.

The unused ambient `[Finite G]`, the two source local subgroup instances
and the redundant `noncomputable section` are omitted. The definition
keeps its own `noncomputable` modifier. The intervening analytic theorems
are not needed to construct `Function.invFun`, so this module does not
import their proof module. Source-order edges in the public M303
partition are scheduling information, not additional premises.
The partition records no patch10 change for this source.

This module contributes one definition. The companion
[`HilbertRamification.HerbrandFunction.Definitions`](../../HilbertRamification/HerbrandFunction/Definitions.md)
contributes the three actual unique-extension definitions in the same
focused unit. Generic inverse laws and order isomorphisms, actual
evaluation/inverse/monotonicity laws, upper-group laws and
inertia/reciprocity conclusions remain separate.

## Sources, license and authorship

The registered original is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
original path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory was
present at preparation.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned originals,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Their inherited notices are preserved unchanged. The root NOTICE inventory
has no entry for this source file.

Worker 106 contributed the source/interface extraction and reuse analysis
in the task contract. Worker 1199 independently checked the pinned source,
published dependencies, licenses and Mathlib construction, implemented
the extraction and wrote this companion on 2 November 2026. The Lean
header records the modifications. The approved environment is Lean 4.34.0
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, distinct from the
source's Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
