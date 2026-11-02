# Finite Herbrand monotonicity, surjectivity and continuity statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFunctionAnalyticStatement`.
It groups M303.026–.028 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L253-L349),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
It formulates the three analytic laws and supplies no proof of them.

The module imports the published normalized
[definitions](Definitions.md) unchanged. Its only additional import is
`Mathlib.Topology.MetricSpace.Pseudo.Defs`, which provides continuity and
the standard real topology through `Real.pseudoMetricSpace`, with distance
`|x - y|`. Both the domain and codomain are the full real line `ℝ`,
with their usual order and topology. No topology is supplied as a parameter.

## Complete proposition and quantifiers

The declaration has exactly the arbitrary universe parameter `u`, has
no value parameters, and returns `Prop`. Within its namespace, its full
defining expression is:

```lean
def HerbrandFunctionAnalyticStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    StrictMono (herbrandFunction F) ∧
    Function.Surjective (herbrandFunction F) ∧
    Continuous (herbrandFunction F)
```

All binders occur inside the proposition. The type `G : Type u` is
implicit; `Group G` and `Finite G` are supplied instance binders; the
filtration `F` is explicit. There are no other binders or hypotheses.
For each supplied filtration the conjunction is right-associated:
strict monotonicity, followed by the conjunction of surjectivity and
continuity.

The first conjunct asserts that for all real `s < t`,
`herbrandFunction F s < herbrandFunction F t`. The second asserts that
every real `y` is `herbrandFunction F s` for some real `s`. The third
asserts continuity everywhere on `ℝ` in the usual real topology.

## Exact source map and finite scope

The original theorem names in this table are relative to
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
Each range includes its source docstring and implementation.

| Conjunct | Source unit and theorem | Source lines | Extracted conclusion |
| --- | --- | --- | --- |
| 1 | M303.026 `herbrandFunction_strictMono` | 253–292 | `StrictMono (herbrandFunction F)` |
| 2 | M303.027 `herbrandFunction_surjective` | 294–344 | `Function.Surjective (herbrandFunction F)` |
| 3 | M303.028 `continuous_herbrandFunction` | 346–349 | `Continuous (herbrandFunction F)` |

Source lines 36–37 introduce implicit `{G : Type u}`, supplied
`[Group G] [Finite G]`, and explicit `F`. All three source laws retain
this ambient finite-group scope; none uses `omit [Finite G]`.
The target preserves precisely that scope, even though the imported
function definitions themselves require no finiteness.

The function is the actual normalized function of the supplied
filtration. Its slope at natural `i` is
`(Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)`.
Its value at a natural index is the prefix sum of these slopes. For
nonnegative real `s`, it uses the affine expression at `Nat.floor s`;
for every negative real, including those below `-1`, it returns `s`.
The target includes the entire real domain and codomain.

The statement requires no `Fintype`, chosen enumeration, arithmetic
extension, termination condition, cutoff, or supplied inverse.
It assumes no positivity, recurrence, monotonicity, surjectivity or
continuity law. The imported generic filtration has no
eventual-triviality condition. In particular, a filtration with a
constant nontrivial tail is within the stated finite-group scope.

## Source proof route and extraction changes

In the original source, strict growth is proved by separating the
nonpositive and nonnegative cases, then using positive slopes within a
unit interval and growth of prefix sums between intervals. Surjectivity
uses the identity branch for nonpositive values; for positive values,
the natural-value lower bound produces a least bracketing interval,
and its affine formula supplies a preimage. Continuity follows from
monotonicity and surjectivity. These are the source proof routes for
a prospective later proof of this target; this module implements none
of those arguments.

The extraction adds the namespace prefix `Langlands.NYLL` and groups
the three theorem signatures, in source order, as one closed
Prop-valued definition. The universal binders move inside the
proposition. The published `Function.Definitions` import replaces the
source arithmetic ramification import and its definition-level imports.
The topology import is reduced to the module providing the usual real
metric topology and continuity predicate; the source monotone-continuity
theorem and further metric lemmas are unnecessary to state this target.
The source local subgroup instances, noncomputable section, theorem
commands and proofs are omitted. No other declaration is introduced.

This unit constructs no inverse or order isomorphism. Proofs of these
laws, later inverse data, arithmetic upper numbering, inertia and
reciprocity results belong to separate units.

## Provenance and attribution

Original source lines 1–349 were read, including the ambient variables,
definitions and all three theorem implementations. The complete
original file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source
path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public M303 partition records no patch10
change.

The original copyright and authorship header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original `Function.lean` has no entry in the root NOTICE inventory.

Worker 106 supplied the source analysis and aggregate target design.
Worker 384 independently checked the source, published definitions and
topology import, and wrote this proposition and companion on
2 November 2026. The Lean header records these changes.
