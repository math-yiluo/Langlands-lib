# Finite basic Herbrand proofs

This module proves the unchanged closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFiniteBasicStatement`.
Its aggregate theorem, in that namespace, has the complete type

```lean
theorem herbrandFiniteBasic : HerbrandFiniteBasicStatement.{u}
```

The sole universe parameter `u` is arbitrary. The theorem has no outer
value parameters, instances or hypotheses. It introduces the target's
implicit group, supplied `Group` and `Finite` instances and explicit
filtration, and constructs its three right-associated conjuncts in order:
the two bounds at one, the closed-interval cardinal-sum formula and
nonnegativity on nonnegative reals.

The proof imports the published [target](FiniteBasicStatement.md) and
[evaluation proof](EvaluationProof.md), together with Mathlib
`Algebra.BigOperators.Ring.Finset` and
`Algebra.Order.BigOperators.Group.Finset` for finite-sum distribution and
nonnegativity. All published pairs remain unchanged. The group is in `Type u`; its filtration consists of actual
antitone normal subgroups with no eventual-triviality condition.

## Helpers and implemented proof

Each helper below takes implicit `{G : Type u}`, supplied `[Group G]`
and `[Finite G]`, and explicit `F : AntitoneNormalSubgroupFiltration G`.
Their names are relative to the declaration namespace above.

| Helper | Further binders and conclusion |
| --- | --- |
| `herbrandFunction_one_pos_le_one` | Proves `0 < herbrandFunction F 1 ∧ herbrandFunction F 1 ≤ 1`. |
| `herbrandFunction_eq_card_sum_of_mem_Icc` | Explicit `m : ℕ`, implicit `s : ℝ`, then proofs `(m : ℝ) ≤ s` and `s ≤ (m : ℝ) + 1`; proves the target's actual cardinal-sum formula. |
| `herbrandFunction_nonneg` | Implicit `s : ℝ` and proof `0 ≤ s`; proves `0 ≤ herbrandFunction F s`. |

For the bounds, the subgroup carriers at indices zero and one are finite
because they are subtypes of the finite group, and nonempty because they
contain the identity. Thus `Nat.card_pos` gives positive natural
cardinalities, and real casts preserve positivity. Antitonicity gives
`F.lower 1 ≤ F.lower 0`. The proof constructs the inclusion between their
carrier types and checks injectivity by taking underlying group values
and applying subtype extensionality. `Nat.card_le_card_of_injective`
then compares the cardinalities. The imported `herbrandFunction_one_eq`
identifies the function value with their ratio. Positive numerator and
denominator give the strict lower bound. Multiplication by the positive
denominator reduces the upper bound to the cardinality comparison.
No positivity or cardinality bound is an additional premise.

For the cardinal formula, the imported `herbrandFunction_eq_on_Icc`
already covers both endpoints of `[m,m+1]` using the slope indexed by `m`.
Unfolding the prefix sum and shifted slopes expresses every term with the
same denominator `D = (Nat.card (F.lower 0) : ℝ)`. Replacing division by
multiplication by `D⁻¹`, factoring that inverse from the finite sum, and
using distributivity and associativity yields exactly

```text
herbrandFunction F s =
  (sum over i < m of |F.lower (i+1)|
    + (s-m) * |F.lower (m+1)|) / |F.lower 0|.
```

Here every cardinality is `Nat.card` cast to `ℝ`. The range is exactly
`Finset.range m` and the entire numerator is divided by the zeroth
subgroup cardinality. The proof performs no denominator cancellation;
this algebraic identity is valid even for a zero denominator under total
real division. The helper nevertheless retains the source and target's
`Finite G` binder.

For nonnegativity, let `m = Nat.floor s`. The hypothesis `0 ≤ s` gives
`(m : ℝ) ≤ s`, and `Nat.lt_floor_add_one s` gives the closed upper bound.
The cardinal-sum helper applies at this natural floor. Every cast
cardinality is nonnegative, so the finite sum is nonnegative. The
fractional factor `s - (m : ℝ)` is nonnegative by the floor lower bound;
its product with the final cardinality is nonnegative. The numerator is
the sum of these nonnegative quantities, and division by a nonnegative
cardinality preserves nonnegativity. This uses neither a separately
published slope/prefix nonnegativity result nor a discrete elementary
aggregate.

The aggregate introduces all of the target's universal binders and
assembles these helpers with the exact conjunction order. There is no
chosen enumeration, extra denominator premise, cutoff, termination,
arithmetic extension, or analytic hypothesis. This unit establishes only
these three finite basic laws; analytic and inverse results, arithmetic
upper numbering, inertia and reciprocity remain separate work.

## Source and adaptations

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L184-L251),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, with whole-file SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
The ambient declarations and original imports at lines 1–56 and all laws
and proofs at lines 175–251 were read for this proof. The registered
source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public M303 partition records no patch10 change.

| Source unit and original law | Lines | Adaptation |
| --- | --- | --- |
| M303.021 `herbrandFunction_one_pos_le_one` | 184–205 | Retains the positive-cardinality and injective-inclusion argument, using `Nat.card_pos`, explicit casts and the published evaluation law. |
| M303.024 `herbrandFunction_eq_card_sum_of_mem_Icc` | 230–243 | Uses the published closed-interval evaluation and direct inverse-denominator distribution, avoiding the original `field_simp` and nonzero-denominator proof. |
| M303.025 `herbrandFunction_nonneg` | 245–251 | Uses the cardinal-sum formula at the natural floor and termwise nonnegativity instead of the original separate slope and prefix-sum helpers. |

All three helpers retain the original finite-group scope. The namespace
gains `Langlands.NYLL`; the original imports are replaced by the two
published modules. The two additional Mathlib imports supply finite-sum lemmas; no subgroup
instance is introduced. The cardinal-sum helper writes its finite-group binders explicitly,
retaining the source interface although its proof uses only total real
arithmetic. Worker 60 implemented these adaptations and the exact closed
aggregate. Worker 106 supplied the original-source analysis, direct proof
route and task design. The imported evaluation proof is reused by Lean
name without copying its authors' proof text.

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
