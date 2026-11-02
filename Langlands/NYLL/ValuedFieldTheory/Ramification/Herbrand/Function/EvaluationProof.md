# Herbrand evaluation and interpolation proofs

This module proves the published closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFunctionEvaluationStatement`.
The sole import is the unchanged
[evaluation statement](EvaluationStatement.md), which imports the
unchanged [normalized definitions](Definitions.md). In their namespace,
the theorem has the complete type

```lean
theorem herbrandFunctionEvaluation :
    HerbrandFunctionEvaluationStatement.{u, v}
```

Here `u` and `v` are arbitrary independent universe parameters. The
theorem has no value parameters, hypotheses or additional instances.
Its first conjunct compares filtrations on `G : Type u` and
`G' : Type v`; its second conjunct proves the eight evaluation and
interpolation laws for every group in `Type u`, in the published order.
The cardinality hypothesis belongs inside the universally quantified
comparison law.

The module also exposes the following source-style helper theorems.
Their names are relative to the namespace above. Each takes implicit
`{G : Type u}`, a supplied `[Group G]`, and explicit
`F : AntitoneNormalSubgroupFiltration G`. None assumes `Finite G`
or `Fintype G`.

| Helper theorem | Further binders and conclusion |
| --- | --- |
| `herbrandFunction_eq_of_card_lower_eq` | Independent implicit `{G' : Type v}`, `[Group G']`, explicit `F'`, a hypothesis equating `Nat.card (F.lower n)` and `Nat.card (F'.lower n)` at every natural index, and explicit real `s`; concludes equality of the two functions at `s`. |
| `herbrandFunction_of_nonpos` | Implicit real `s` and explicit proof `s ≤ 0`; concludes `herbrandFunction F s = s`. |
| `herbrandFunction_zero` | Concludes `herbrandFunction F 0 = 0`. |
| `herbrandFunction_neg_one` | Concludes `herbrandFunction F (-1) = -1`. |
| `herbrandFunction_of_floor` | Implicit real `s`, explicit proof `0 ≤ s`, explicit natural `m` and proof `Nat.floor s = m`; concludes the affine expression at index `m`. |
| `herbrandFunction_nat` | Explicit natural `n`; concludes `herbrandFunction F (n : ℝ) = herbrandValueNat F n`. |
| `herbrandFunction_one_eq` | Concludes `herbrandFunction F 1 = (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0)`. |
| `herbrandFunction_eq_on_Ico` | Explicit natural `m`, implicit real `s` and explicit proofs `(m : ℝ) ≤ s` and `s < (m : ℝ) + 1`; concludes the affine expression at index `m`. |
| `herbrandFunction_eq_on_Icc` | The same binders with `s ≤ (m : ℝ) + 1`; concludes the same expression, including at the right endpoint. |

The zero, minus-one and natural-point helpers have the `simp` attribute.
The closed aggregate theorem instantiates these helpers and constructs
the two conjunctions directly.

## Implemented proof

For the comparison law, the cardinality hypothesis identifies the
numerators and denominators in every `herbrandSlope`. Substitution
then identifies every finite prefix sum `herbrandValueNat`. A case
split on `0 ≤ s` identifies the affine expressions in the nonnegative
branch and the two identical values `s` in the negative branch. This
argument compares actual subgroup carriers through their `Nat.card`
values and does not identify the groups or their universes.

For a nonpositive argument, the proof separates equality with zero
from strict negativity. At zero, natural floor and the empty prefix sum
simplify to zero. At a negative real the branch test is false, so the
definition returns `s`. This covers every negative real, including
those below `-1`. The zero and minus-one helpers specialize this law.

For `0 ≤ s` with `Nat.floor s = m`, unfolding the function and
substituting the floor equality gives

```lean
herbrandFunction F s =
  herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m
```

The index uses natural floor `⌊s⌋₊`, not integer floor. At a natural
argument `n`, natural floor is `n` and the affine correction vanishes.
The natural-point helper follows by simplification of the definition.

At one, the proof first rewrites the argument as the real cast of the
natural number one and applies natural-point evaluation. Unfolding
the prefix sum gives its single term `herbrandSlope F 0`; unfolding
that slope gives exactly
`(Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0)`.
The proof uses no subgroup `Fintype` instance, cardinal positivity,
division cancellation or nonzero-denominator assumption. It remains
valid under total real division when `Nat.card (F.lower 0) = 0`.

On `[m,m+1)`, the lower bound gives nonnegativity because `m` is a
natural number. Mathlib's `Nat.floor_eq_iff` turns the two interval
inequalities into `Nat.floor s = m`; the floor helper supplies the
affine expression.

On `[m,m+1]`, the proof separates the right endpoint from strict
inequality. The strict case uses the half-open interval helper.
At `s = (m : ℝ) + 1`, natural-point evaluation changes the left side
to `herbrandValueNat F (m + 1)`. Unfolding the prefix sums and applying
`Finset.sum_range_succ` gives

```lean
herbrandValueNat F (m + 1) =
  herbrandValueNat F m + herbrandSlope F m
```

The fractional factor on the right is one. Simplification proves the
endpoint equality while retaining the slope indexed by `m`, even
though the defining natural floor at the endpoint is `m + 1`.
The recurrence is proved directly where used; this module does not
depend on a separate discrete elementary proof.

All these arguments use the published actual lower subgroups,
`Nat.card`, finite sums and total real arithmetic. They require no
positivity, arithmetic extension, subgroup enumeration or eventual
termination condition. This module proves the nine evaluation laws;
it makes no claim of strict monotonicity, surjectivity, continuity or
the existence of an inverse.

## Source and adaptations

The proof route is adapted from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L120-L228),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The whole-file SHA-256 is
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Original lines 1–228 were read, including the section variables,
local instances, definitions and the excluded positivity law M303.021.

| Source unit | Original declaration | Source lines | Implemented adaptation |
| --- | --- | --- | --- |
| M303.014 | `herbrandFunction_eq_of_card_lower_eq` | 120–140 | Retains the slope/prefix comparison and branch split; names the independent universes `u` and `v`. |
| M303.015 | `herbrandFunction_of_nonpos` | 142–149 | Retains the zero/negative split; unfolds the empty prefix sum directly at zero. |
| M303.016 | `herbrandFunction_zero` | 151–154 | Specializes the nonpositive helper. |
| M303.017 | `herbrandFunction_neg_one` | 156–159 | Specializes the nonpositive helper, simplifying the numerical inequality. |
| M303.018 | `herbrandFunction_of_floor` | 161–167 | Retains the definition and floor substitution. |
| M303.019 | `herbrandFunction_nat` | 169–173 | Retains direct simplification at natural arguments. |
| M303.020 | `herbrandFunction_one_eq` | 175–182 | Strengthens the source interface by omitting its finite-group premise; evaluates the single-term prefix directly. |
| M303.022 | `herbrandFunction_eq_on_Ico` | 207–215 | Retains the nonnegativity and natural-floor argument. |
| M303.023 | `herbrandFunction_eq_on_Icc` | 217–228 | Retains the endpoint/strict split; unfolds the prefix sum and applies `Finset.sum_range_succ` directly at the endpoint. |

The source's M303.020 retains its ambient `[Finite G]`; it has no
`omit [Finite G]` command, and its simplification can use the source's
local subgroup `Fintype` instance. The published target deliberately
strengthens that interface. The unrestricted one-term-sum argument
above proves precisely that stronger clause. The other eight source
laws already omit the finite-group instance.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
source path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the workspace, project or supplied
Library errata lookup. The public M303 source partition records no
patch10 change.

The namespace gains `Langlands.NYLL`. The sole import replaces the
source imports with the published aggregate statement, whose
definition imports supply all required Mathlib tools. No new instance
or additional import is introduced. The source's ambient finite-group
assumption and local subgroup instances are omitted. Cast and
endpoint simplifications use `simp`; no numerical tactic import is
needed. The target pair, definitions pair, generic filtration pair
and license files remain unchanged.

The original copyright and authorship header is preserved verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Worker 106 supplied the source analysis, proof route and aggregate
target design. Worker 1199 read the original source, adapted and
checked the Lean proofs, assembled the closed theorem, and wrote this
companion on 2 November 2026.
