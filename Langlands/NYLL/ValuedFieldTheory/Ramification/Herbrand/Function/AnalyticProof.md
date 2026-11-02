# Finite Herbrand monotonicity, surjectivity and continuity proofs

This module proves the unchanged closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFunctionAnalyticStatement`.
Its aggregate theorem, in that namespace, has the complete type

```lean
theorem herbrandFunctionAnalytic : HerbrandFunctionAnalyticStatement.{u}
```

The sole universe parameter `u` is arbitrary. The theorem has no outer
value parameters, instances or hypotheses. It introduces the target's
implicit group `G : Type u`, the supplied `Group G` and `Finite G`
instances and the explicit filtration `F`, and constructs the three
right-associated conjuncts in order: `StrictMono (herbrandFunction F)`,
`Function.Surjective (herbrandFunction F)` and
`Continuous (herbrandFunction F)`. Domain and codomain are the whole real
line with its usual order and topology.

The proof imports the published [target](AnalyticStatement.md),
[evaluation proof](EvaluationProof.md),
[finite basic proof](FiniteBasicProof.md) and
[discrete elementary proof](DiscreteElementaryProof.md). From Mathlib it
imports `Topology.Order.MonotoneContinuity` for continuity of monotone
surjections, `Topology.MetricSpace.Pseudo.Lemmas` for the instance
`OrderTopology ℝ` (that the metric topology on `ℝ` is its order
topology), and the `field_simp`, `linarith` and `ring` tactics. All
published pairs, including the target pair, remain unchanged. The
filtration consists of actual antitone normal lower subgroups with no
eventual-triviality condition.

## Helpers

Each helper takes implicit `{G : Type u}`, supplied `[Group G]` and
`[Finite G]`, and explicit `F : AntitoneNormalSubgroupFiltration G`, and
has no further binders. Names are relative to the namespace above.

| Helper | Conclusion |
| --- | --- |
| `herbrandFunction_strictMono` | `StrictMono (herbrandFunction F)` |
| `herbrandFunction_surjective` | `Function.Surjective (herbrandFunction F)` |
| `continuous_herbrandFunction` | `Continuous (herbrandFunction F)` |

The imported results used below are, from the evaluation proof,
`herbrandFunction_of_nonpos` (identity at nonpositive reals),
`herbrandFunction_eq_on_Ico` and `herbrandFunction_eq_on_Icc` (the affine
formula `herbrandValueNat F m + (s - m) * herbrandSlope F m` on `[m, m+1)`
and on `[m, m+1]`); from the finite basic proof, `herbrandFunction_nonneg`;
and from the discrete elementary proof, `herbrandValueNat_zero`,
`herbrandValueNat_succ`, `herbrandSlope_pos`, `herbrandSlope_nonneg`,
`nat_div_card_le_herbrandValueNat` and `herbrandValueNat_strictMono`.

## Strict monotonicity

Let `s < t`. The proof separates three cases.

1. If `t ≤ 0`, then also `s ≤ 0`, so both values are the arguments
   themselves by the identity branch, and the claim is `s < t`.
2. If `s < 0 < t`, the value at `s` is `s < 0`, while the value at `t`
   is nonnegative by `herbrandFunction_nonneg`.
3. Otherwise `0 ≤ s < t`. Let `m = ⌊s⌋₊` and `n = ⌊t⌋₊`; the floor
   bounds give `m ≤ s < m + 1` and `n ≤ t < n + 1`, and monotonicity of
   the floor gives `m ≤ n`. Both values are rewritten by the half-open
   affine formula.
   - If `m = n`, the two affine expressions share the prefix value and
     the positive slope `herbrandSlope F m`, so `nlinarith` concludes from
     `s < t` and positivity of the slope.
   - If `m < n`, then `s - m < 1` and positivity of the slope give that
     the value at `s` is strictly below
     `herbrandValueNat F m + herbrandSlope F m = herbrandValueNat F (m + 1)`
     (prefix recurrence). Since `m + 1 ≤ n`, monotonicity of the
     natural prefix sums gives `herbrandValueNat F (m + 1) ≤
     herbrandValueNat F n`. Finally the value at `t` is at least
     `herbrandValueNat F n`, because `t - n ≥ 0` and the slope at `n` is
     nonnegative. Chaining these inequalities proves the claim.

## Surjectivity

Let `y` be real. If `y ≤ 0`, the identity branch gives
`herbrandFunction F y = y`. Assume `0 < y` and let
`d = (Nat.card (F.lower 0) : ℝ)`, which is positive because the finite
subgroup is nonempty (`Finite.card_pos`). The Archimedean property gives
a natural `N > y * d`, so `y ≤ N / d ≤ herbrandValueNat F N` by the
natural cardinal lower bound. Hence some natural `k` has
`y ≤ herbrandValueNat F k`; let `n` be the least one (`Nat.find`, whose
decidability comes from the order on `ℝ`). Since `herbrandValueNat F 0 = 0 < y`, the index
`n` is positive; write `n = m + 1`. Minimality gives
`herbrandValueNat F m < y`, and the prefix recurrence turns
`y ≤ herbrandValueNat F n` into
`y ≤ herbrandValueNat F m + herbrandSlope F m`.

Define

```text
x = m + (y - herbrandValueNat F m) / herbrandSlope F m.
```

The quotient is nonnegative, so `m ≤ x`; it is at most one by division
by the positive slope, so `x ≤ m + 1`. The closed-interval affine formula
at `m` then evaluates `herbrandFunction F x`, and clearing the nonzero
slope by `field_simp` followed by `ring` shows that this value is `y`.

## Continuity and aggregate

A monotone surjection between linearly ordered spaces with their order
topologies, where the codomain is densely ordered, is continuous
(Mathlib `Monotone.continuous_of_surjective`). Strict monotonicity gives
monotonicity, so continuity follows from the two previous helpers; the
order-topology instance on `ℝ` is supplied by the imported metric
lemmas module.

The aggregate introduces all of the target's universal binders and
assembles the three helpers in the target's exact conjunction order.
No cutoff, eventual triviality, arithmetic extension, inverse, numerical
bound or analytic law is an extra premise. This unit constructs no
inverse Herbrand function or order isomorphism; inverse data, arithmetic
upper numbering, inertia and reciprocity remain separate work.

## Source and adaptations

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L253-L349),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, with whole-file SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
The ambient declarations and original imports at lines 1–56 and the three
laws and their proofs at lines 253–349 were read for this proof. The
registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public M303 partition records no patch10 change.

| Source unit and original law | Lines | Adaptation |
| --- | --- | --- |
| M303.026 `herbrandFunction_strictMono` | 253–292 | Same three-case route; local `let` bindings become `set`, and the half-open upper floor bound uses `Nat.lt_floor_add_one`. |
| M303.027 `herbrandFunction_surjective` | 294–344 | Same least-bracketing-index route; local `let` bindings become `set` (`have` for the existence proof), and an unused positivity binding is dropped. |
| M303.028 `continuous_herbrandFunction` | 346–349 | Unchanged one-line proof. |

All three helpers retain the original finite-group scope. The namespace
gains `Langlands.NYLL`. The original imports are replaced by the four
published modules, the two Mathlib topology modules that the source also
imports, and explicit tactic imports. The source local subgroup
instances and noncomputable section are omitted; no subgroup instance is
introduced. The published helpers are reused by Lean name.

Worker 1237 implemented these adaptations and the exact closed aggregate.
Worker 106 supplied the original-source analysis, proof route and task
design.

The original copyright and authorship header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.
