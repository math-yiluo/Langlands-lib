# Herbrand evaluation and interpolation statement

This module defines the closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandFunctionEvaluationStatement`.
It packages the nine elementary comparison, value and interpolation laws
M303.014–.020 and M303.022–.023 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L120-L228),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The value-at-one clause is a source-derived strengthening that removes
the original lemma's finite-group premise, as explained below.
It formulates these laws and supplies no proof of them.

The sole import is the published normalized
[definitions module](Definitions.md). Its `herbrandSlope`,
`herbrandValueNat` and `herbrandFunction`, and the generic
`AntitoneNormalSubgroupFiltration` they use, are unchanged.

## Complete proposition and binders

The declaration has exactly the independent arbitrary universe parameters
`u` and `v`, has no value parameters, and returns `Prop`. In its namespace,
the complete defining expression is:

```lean
def HerbrandFunctionEvaluationStatement : Prop :=
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
      {G' : Type v} [Group G'] (F' : AntitoneNormalSubgroupFiltration G')
      (_hcard : ∀ n : ℕ, Nat.card (F.lower n) = Nat.card (F'.lower n))
      (s : ℝ),
      herbrandFunction F s = herbrandFunction F' s) ∧
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ (s : ℝ), s ≤ 0 → herbrandFunction F s = s) ∧
    herbrandFunction F 0 = 0 ∧
    herbrandFunction F (-1) = -1 ∧
    (∀ (s : ℝ), 0 ≤ s → ∀ (m : ℕ), Nat.floor s = m →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m) ∧
    (∀ (n : ℕ), herbrandFunction F (n : ℝ) = herbrandValueNat F n) ∧
    herbrandFunction F 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) ∧
    (∀ (m : ℕ) (s : ℝ), (m : ℝ) ≤ s → s < (m : ℝ) + 1 →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m) ∧
    (∀ (m : ℕ) (s : ℝ), (m : ℝ) ≤ s → s ≤ (m : ℝ) + 1 →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m))
```

The outer conjunction has two independently quantified blocks. In the
first block, the group types `G : Type u` and `G' : Type v` are implicit,
their `Group` structures are supplied instances, and `F` and `F'` are
explicit. The groups and universes are independent. The explicit
hypothesis `_hcard` (the source's `hcard`) equates the actual subgroup
cardinalities at every natural index `n`; that index is explicit inside
`_hcard`. The real
argument `s` is explicit. All of these binders are inside the proposition.
In particular, `_hcard` is a premise of the universally quantified
comparison law, not a parameter or a global assumption of the target.

The second block independently binds implicit `G : Type u`, a supplied
`Group G` instance, and explicit `F`. It then takes the eight conjuncts
in the displayed order. The first binds explicit real `s` and assumes
`s ≤ 0`. The fourth binds explicit real `s`, assumes `0 ≤ s`, then
binds explicit natural `m` and assumes `Nat.floor s = m`. The fifth
binds explicit natural `n`. Each of the last two binds explicit natural
`m`, then explicit real `s`, and assumes the two displayed interval
inequalities. The other three conjuncts have no further binders.
Each displayed arrow universally quantifies its proof premise.

## Source-to-conjunct map

The original namespace is
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
The theorem names below are relative to that namespace. The source
ranges include the surrounding finiteness-scope commands and docstrings
where present.

| Position in the proposition | Source unit and theorem | Source lines | Content |
| --- | --- | --- | --- |
| First universal block | M303.014 `herbrandFunction_eq_of_card_lower_eq` | 120–140 | Equal lower-group cardinalities imply equality at every real argument, for two independent group types. |
| Second block, conjunct 1 | M303.015 `herbrandFunction_of_nonpos` | 142–149 | The value is `s` whenever `s ≤ 0`. |
| Second block, conjunct 2 | M303.016 `herbrandFunction_zero` | 151–154 | The value at zero is zero. |
| Second block, conjunct 3 | M303.017 `herbrandFunction_neg_one` | 156–159 | The value at `-1` is `-1`. |
| Second block, conjunct 4 | M303.018 `herbrandFunction_of_floor` | 161–167 | For `0 ≤ s` and natural floor `m`, the value is the affine expression at `m`. |
| Second block, conjunct 5 | M303.019 `herbrandFunction_nat` | 169–173 | The value at natural `n`, cast to `ℝ`, is `herbrandValueNat F n`. |
| Second block, conjunct 6 | Derived strengthening of M303.020 `herbrandFunction_one_eq` | 175–182 | The value at one is the actual cardinality ratio at indices one and zero; this target removes the source lemma's `Finite G` premise. |
| Second block, conjunct 7 | M303.022 `herbrandFunction_eq_on_Ico` | 207–215 | The affine expression holds for `m ≤ s < m + 1`. |
| Second block, conjunct 8 | M303.023 `herbrandFunction_eq_on_Icc` | 217–228 | The same expression holds for `m ≤ s ≤ m + 1`, including the right endpoint, with slope `herbrandSlope F m`. |

The eight source laws M303.014–.019 and M303.022–.023 explicitly use
`omit [Finite G]` and have unrestricted group scope. M303.020 instead
retains the ambient `[Finite G]` introduced at source line 36: it has
no `omit` command, and its original elaborated interface includes that
instance. The source's local subgroup `Fintype` instance at lines 39–40
allows its `simp` proof to use finite-cardinality simplifications.
Thus the unrestricted value-at-one clause here strengthens that source
interface.

This strengthening follows from the actual published definitions.
At `s = 1`, the natural floor is `1` and the affine correction is zero,
so the defining value is `herbrandValueNat F 1`. Its prefix sum has
the single term `herbrandSlope F 0`, which is exactly
`(Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0)`.
This argument uses neither finiteness nor cardinal positivity and is
valid for total real division even when the denominator is zero.
It gives the provenance rationale for the stronger clause; this module
only defines the aggregate target and includes no proof.
The intervening positivity and upper-bound law M303.021 is excluded.

The original source lines 1–228 were read, including the definitions,
section variables, local instances, and the excluded M303.021. The
complete source file has SHA-256
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

## Scope and extraction changes

Every term uses the published actual subgroup carriers and `Nat.card`.
The slope at `m` is
`(Nat.card (F.lower (m + 1)) : ℝ) / Nat.card (F.lower 0)`.
The natural values are its prefix sums; the real function uses
`Nat.floor s` on its nonnegative branch and the identity on every
negative real, including those below `-1`.
The last conjunct includes `s = (m : ℝ) + 1` while retaining slope `m`.

Neither block assumes `Finite`, `Fintype`, positivity, a nonzero
denominator, an arithmetic extension, an enumeration, or a termination
cutoff. `Nat.card` and real division are total, so the stated value
identities include cases where a subgroup cardinality is zero.
The generic filtration itself has no eventual-triviality condition.

The extraction adds the namespace prefix `Langlands.NYLL`, replaces the
original imports by the published definitions import, and packages the
nine source theorem conclusions as one closed `Prop` definition.
Source implicit real binders become explicit universal binders inside
the proposition; local hypotheses and index binders retain the
mathematical order stated above. The source's comparison `Type*` is
made the independently named universe `v`. For M303.020, the extraction
also removes the source lemma's inferred `[Finite G]` premise and
states the stronger identity justified by the definitions above.
The other eight laws preserve their source group scopes. No original
proof, local subgroup instance, ambient finite-group assumption or
theorem attribute is included. No additional declaration is introduced.

This statement does not establish the nine laws. Proofs, finite
positivity bounds, the cardinal-sum formula, monotonicity, surjectivity,
continuity, inverse data, arithmetic wrappers, inertia and reciprocity
are outside this unit.

## Attribution

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
Worker 1199 independently read the original source, checked the
published interfaces and attribution, and wrote the proposition and
this companion on 2 November 2026. The Lean header records these changes.
