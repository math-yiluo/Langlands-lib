# Finite basic Herbrand statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFiniteBasicStatement`.
It groups M303.021 and M303.024–.025 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L184-L251),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
It defines a target proposition and proves none of its three assertions.

The sole import is the published normalized
[definitions module](Definitions.md). Its Lean/Markdown pair and all
imported pairs are unchanged. The function and subgroup carriers are the
published `herbrandFunction` and `AntitoneNormalSubgroupFiltration`.

## Complete proposition and quantifiers

The declaration has only the arbitrary universe parameter `u`, has no
value parameters, and returns `Prop`. With its declaration namespace and
`BigOperators` scope open, the complete defining expression is:

```lean
def HerbrandFiniteBasicStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (0 < herbrandFunction F 1 ∧ herbrandFunction F 1 ≤ 1) ∧
    (∀ (m : ℕ) {s : ℝ}, (m : ℝ) ≤ s → s ≤ (m : ℝ) + 1 →
      herbrandFunction F s =
        ((∑ i ∈ Finset.range m, (Nat.card (F.lower (i + 1)) : ℝ)) +
          (s - (m : ℝ)) * (Nat.card (F.lower (m + 1)) : ℝ)) /
          (Nat.card (F.lower 0) : ℝ)) ∧
    (∀ {s : ℝ}, 0 ≤ s → 0 ≤ herbrandFunction F s)
```

The implicit type `G : Type u`, supplied `Group G` and `Finite G`
instances, and explicit filtration `F` are universal binders inside
the closed proposition. They scope over all three conjuncts. Writing
these conjuncts as `A`, `B` and `C`, the grouping is `A ∧ (B ∧ C)`;
the first conjunct `A` is itself the pair of strict positivity and the
upper bound at one, in that order.

The second conjunct universally binds explicit `m : ℕ`, then implicit
`s : ℝ`, followed by the two interval premises in the displayed order.
Each arrow universally quantifies its proof premise. Both endpoints are
included: `(m : ℝ) ≤ s ≤ (m : ℝ) + 1`. At the right endpoint the formula
still uses the prefix through `i < m` and the subgroup at `m + 1`.
The third conjunct independently binds implicit `s : ℝ`, then the
premise `0 ≤ s`, and concludes nonnegativity.

The numerator's prefix is the actual finite sum over
`i ∈ Finset.range m`, namely all natural indices `i < m`.
Every summand is the real cast of `Nat.card (F.lower (i + 1))`.
The interpolation term uses `s - (m : ℝ)` multiplied by the real cast
of `Nat.card (F.lower (m + 1))`. The entire numerator is divided by
the real cast of the actual zeroth subgroup cardinality
`Nat.card (F.lower 0)`. These are cardinalities of the published
subgroup carrier types, with the source's shifted indices.

## Source map and finite scope

All source theorem names below are relative to
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
The ranges include their docstrings and proofs; only their signatures
are extracted.

| Conjunct | Source unit and theorem | Source lines | Target content |
| --- | --- | --- | --- |
| 1 | M303.021 `herbrandFunction_one_pos_le_one` | 184–205 | `0 < herbrandFunction F 1 ∧ herbrandFunction F 1 ≤ 1`. |
| 2 | M303.024 `herbrandFunction_eq_card_sum_of_mem_Icc` | 230–243 | The displayed actual cardinal-sum formula for every natural `m` and implicit real `s` in the closed interval. |
| 3 | M303.025 `herbrandFunction_nonneg` | 245–251 | For every implicit real `s`, `0 ≤ s` implies `0 ≤ herbrandFunction F s`. |

The original section at lines 36–37 supplies implicit `G : Type u`,
`Group G`, `Finite G`, and explicit `F`. All three source laws retain
that ambient finite-group scope; none has an `omit [Finite G]` command.
The single outer universal block preserves it for all three conjuncts,
including the cardinal-sum formula and nonnegativity. The unrestricted
scope of the imported data definitions and some separately packaged
evaluation laws does not remove this finite-group binder.

There is no further `Fintype`, chosen enumeration, arithmetic extension,
eventual-triviality cutoff, normalized initial subgroup, nonzero
denominator premise, or assumed bound. The filtration is the generic
antitone normal subgroup filtration, whose structure has no termination
condition. The existing cutoff-based Herbrand polygon and actual
p-adic specialization do not replace this arbitrary finite-group
interface.

## Provenance and extraction changes

Source lines 1–251 were read, including the section variables, local
instances, definitions and the three selected statements and proofs.
The complete original file has SHA-256
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
change for this source module.

The extraction adds the namespace prefix `Langlands.NYLL`, replaces
the original imports by the published `Function.Definitions` import,
and opens finite-sum notation explicitly. It converts three theorem
signatures into one closed `Prop` definition with the stated
right-associated conjunction. The group, instance and filtration
binders are written explicitly inside the proposition. Natural indices,
implicit real binders and interval premises retain their source order;
the numerical casts are displayed explicitly. The source proofs, local
subgroup instances and theorem commands are omitted.

Proofs, analytic laws, inverse data, upper groups, arithmetic wrappers,
inertia and reciprocity belong to separate units.

## Attribution

The original copyright and authorship header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain byte-identical
to the pinned originals, with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original `Function.lean` has no entry in the root NOTICE inventory.

Worker 106 supplied the source analysis and aggregate target design.
Worker 60 independently checked the pinned original, published
definitions and attribution, and wrote the proposition and this
companion on 2 November 2026. The Lean header records these changes.
