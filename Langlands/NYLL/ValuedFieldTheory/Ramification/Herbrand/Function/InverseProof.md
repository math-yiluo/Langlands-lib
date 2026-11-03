# Finite inverse Herbrand laws proofs

This module proves the unchanged closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandInverseLawsStatement`.
Its aggregate theorem, in that namespace, has the complete type

```lean
theorem herbrandInverseLaws : HerbrandInverseLawsStatement.{u}
```

The sole universe parameter `u` is arbitrary. The theorem has no outer
value parameters, instances or hypotheses. It introduces the target's
implicit group `G : Type u`, the supplied `Group G` and `Finite G`
instances and the explicit filtration `F`, and constructs the seven
right-associated conjuncts in order. Writing `φ = herbrandFunction F` and
`ψ = inverseHerbrandFunction F`, these are `φ (ψ t) = t` for every real
`t`; `ψ (φ s) = s` for every real `s`; `StrictMono ψ`;
`Function.Surjective ψ`; `Continuous ψ`; `φ s ∈ Set.Ici (-1) ↔
s ∈ Set.Ici (-1)` for every real `s`; and `ψ t ∈ Set.Ici (-1) ↔
t ∈ Set.Ici (-1)` for every real `t`. Domain and codomain are the whole
real line with its usual order and topology. Here `φ` is the published
normalized [Herbrand function](Definitions.md) and `ψ` is the published
[inverse](InverseDefinition.md) `Function.invFun φ`.

The proof imports the published [target](InverseStatement.md) and
[analytic proof](AnalyticProof.md); the latter imports the published
[evaluation proof](EvaluationProof.md). From Mathlib it imports
`Topology.Order.MonotoneContinuity` for continuity of monotone
surjections and `Topology.MetricSpace.Pseudo.Lemmas` for the instance
`OrderTopology ℝ` (that the metric topology on `ℝ` is its order
topology); both are also imported by the analytic proof and are listed
explicitly here. All published pairs, including the target pair, remain
unchanged. The filtration consists of actual antitone normal lower
subgroups with no eventual-triviality condition.

## Helpers

Each helper takes implicit `{G : Type u}`, supplied `[Group G]` and
`[Finite G]`, and explicit `F : AntitoneNormalSubgroupFiltration G`.
The two composition identities take an explicit real argument, the two
half-line equivalences an implicit one, and the other three helpers no
further binder. Names are relative to the namespace above.

| Helper | Further binder | Conclusion |
| --- | --- | --- |
| `herbrandFunction_inverseHerbrandFunction` (`@[simp]`) | `(t : ℝ)` | `herbrandFunction F (inverseHerbrandFunction F t) = t` |
| `inverseHerbrandFunction_herbrandFunction` (`@[simp]`) | `(s : ℝ)` | `inverseHerbrandFunction F (herbrandFunction F s) = s` |
| `inverseHerbrandFunction_strictMono` | none | `StrictMono (inverseHerbrandFunction F)` |
| `inverseHerbrandFunction_surjective` | none | `Function.Surjective (inverseHerbrandFunction F)` |
| `continuous_inverseHerbrandFunction` | none | `Continuous (inverseHerbrandFunction F)` |
| `herbrandFunction_mem_Ici_neg_one_iff` | `{s : ℝ}` | `herbrandFunction F s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1)` |
| `inverseHerbrandFunction_mem_Ici_neg_one_iff` | `{t : ℝ}` | `inverseHerbrandFunction F t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1)` |

The imported results used below are, from the analytic proof,
`herbrandFunction_strictMono`, `herbrandFunction_surjective` (and,
through strict monotonicity, injectivity of `φ`); and from the
evaluation proof, `herbrandFunction_neg_one`, that is `φ (-1) = -1`.

## Composition identities

`ψ` is by definition `Function.invFun φ`. Since `φ` is surjective,
Mathlib's `Function.rightInverse_invFun` gives `φ (ψ t) = t` for every
real `t`. Since `φ` is strictly monotone, hence injective,
`Function.leftInverse_invFun` gives `ψ (φ s) = s` for every real `s`.
Both identities carry the `@[simp]` attribute, as in the source.

## Strict monotonicity and surjectivity

Let `s < t`. Strict monotonicity of `φ` reflects order:
`φ a < φ b ↔ a < b`, so it suffices to show `φ (ψ s) < φ (ψ t)`.
Simplification with the first composition identity reduces this to the
hypothesis `s < t`.

For surjectivity, a real `s` is the value of `ψ` at `φ s` by the second
composition identity.

## Continuity

A monotone surjection between linearly ordered spaces with their order
topologies, where the codomain is densely ordered, is continuous
(Mathlib `Monotone.continuous_of_surjective`). Strict monotonicity of `ψ`
gives monotonicity, so continuity follows from the two previous helpers;
the order-topology instance on `ℝ` is supplied by the imported metric
lemmas module.

## Half-line equivalences

Membership in `Set.Ici (-1)` is unfolded definitionally to `-1 ≤ ·`.
For `φ`, strict monotonicity gives `φ (-1) ≤ φ s ↔ -1 ≤ s`, and
rewriting `φ (-1) = -1` turns its left side into `-1 ≤ φ s`.

For `ψ`, the second composition identity at `-1`, rewritten by
`φ (-1) = -1`, gives `ψ (-1) = -1`. Strict monotonicity of `ψ` gives
`ψ (-1) ≤ ψ t ↔ -1 ≤ t`, and rewriting `ψ (-1) = -1` concludes.

## Aggregate

The aggregate introduces all of the target's universal binders and
assembles the seven helpers in the target's exact conjunction order.
The two half-line conjuncts quantify their real variable explicitly, so
they are supplied as functions of that variable which call the helpers
with the implicit argument inferred. No cutoff, eventual triviality,
arithmetic extension, inverse identity, injectivity, surjectivity,
continuity or order law is an extra premise. This unit constructs no
order isomorphism; the intervening source data M303.035 is not needed
for these laws. Actual-field unique-extension laws, arithmetic upper
numbering, inertia and reciprocity remain separate work.

## Source and adaptations

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L355-L408),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, with whole-file SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
The ambient declarations and original imports at lines 1–70 and the
continuity, inverse and order-isomorphism passage at lines 335–408 were
read for this proof. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public M303 partition records no patch10 change.

| Source unit and original law | Lines | Adapted helper and aggregate conjunct |
| --- | --- | --- |
| M303.030 `herbrandFunction_inverseHerbrandFunction` | 355–358 | Same name and proof; conjunct 1. |
| M303.031 `inverseHerbrandFunction_herbrandFunction` | 360–363 | Same name and proof; conjunct 2. |
| M303.032 `inverseHerbrandFunction_strictMono` | 365–369 | Same name and proof; conjunct 3. |
| M303.033 `inverseHerbrandFunction_surjective` | 371–374 | Same name and proof; conjunct 4. |
| M303.034 `continuous_inverseHerbrandFunction` | 376–379 | Same name and proof; conjunct 5. |
| M303.036 `herbrandFunction_mem_Ici_neg_one_iff` | 390–396 | Same name and proof; conjunct 6, by abstraction over `s`. |
| M303.037 `inverseHerbrandFunction_mem_Ici_neg_one_iff` | 398–408 | Same name and proof; conjunct 7, by abstraction over `t`. |

All seven helpers retain the original finite-group scope, binder
explicitness and proofs; the only textual changes are dropped redundant
parentheses around the partially applied functions and helpers (for
example `herbrandFunction F s` for `(herbrandFunction F) s` and
`herbrandFunction_neg_one F` for `(herbrandFunction_neg_one F)`) and one
line break in the surjectivity signature. The namespace gains `Langlands.NYLL`.
The original imports are replaced by the published target and analytic
proof and the two Mathlib topology modules that the source also imports.
The source local subgroup instances and noncomputable section are
omitted; no subgroup instance is introduced. The source definition
M303.029 `inverseHerbrandFunction` is imported from its published module,
and the order isomorphism M303.035 `herbrandOrderIso` (lines 383–388)
is outside this unit. The published helpers are reused by Lean name.

Worker 1237 implemented these adaptations and the exact closed aggregate.
Worker 106 supplied the original-source analysis, exact-target and
helper design and proof-route analysis.

The original copyright and authorship header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is Apache-2.0; the module docstring records the changes. The
existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.
