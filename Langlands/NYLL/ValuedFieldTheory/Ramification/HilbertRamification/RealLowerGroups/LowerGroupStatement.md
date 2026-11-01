# Elementary real lower ramification laws: statement

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupStatement`
defines the closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.LowerRamificationGroupPropertiesStatement.{u, v, w, x}`.
It groups the six mathematical conclusions in NYLL M304.023–.029 about the
published genuine real lower ramification subgroup. This is a statement
target; this module proves none of these laws and installs no normality
instance.

## Complete internal telescope

The declaration has type `Prop`, with no mathematical parameters outside
its body. Its four universe parameters `u, v, w, x` are independent. The
body universally quantifies the following complete telescope before
forming the conjunction:

```lean
∀ {K : Type u} {L : Type w}
  [Field K] [Field L] [Algebra K L]
  {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
  {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
  [base.valuation.HasExtension target.valuation]
  (huniq :
    Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
      base target), ...
```

The field carriers have universes `u, w`; their chosen value groups have
universes `v, x`. The supplied extension instance refers to the algebra
map of the supplied `Algebra K L`. The uniqueness predicate compares the
chosen target valuation with every extending valuation whose value group
is in `Type x`, exactly the specialization `u, v, w, x, x`.
There is no completeness, finite-dimensionality, separability or
`IsGalois` assumption, and no assumed preservation, normality, filtration
or endpoint law.

## The six conclusions

In this paragraph only, write
`G(s) = lowerRamificationGroup (base := base) (target := target) huniq s`
and
`e(σ) = valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.
All these short names denote the existing public objects in
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`; the Lean
statement refers to them directly. The conjunction is associated to the
right and has exactly the following six clauses, in this order.

1. For every `s : ℝ` and `σ : Gal(L/K)`,
   `σ ∈ G(s) ↔ ∀ a : target.valuationSubring, e(σ)(a) - a ∈ realRamificationIdeal target s`.
2. For every `n : ℕ` and `σ : Gal(L/K)`,
   `σ ∈ G((n : ℝ)) ↔ ∀ a : target.valuationSubring, e(σ)(a) - a ∈ target.maximalIdeal ^ (n + 1)`.
   The quantifier includes `n = 0`.
3. `Antitone (lowerRamificationGroup (base := base) (target := target) huniq)`.
   Thus every pair of real indices `s ≤ t` is required to satisfy `G(t) ≤ G(s)`.
4. For every `s : ℝ`, `(G(s)).Normal`.
5. `G(-1) = ⊤`, where the top subgroup is that of `Gal(L/K)`.
6. For every implicit `{s : ℝ}`, `s ≤ -1 → G(s) = ⊤`.

The actual group `Gal(L/K)` is Mathlib's algebra automorphism group
`L ≃ₐ[K] L`. Every displacement is computed in the actual chosen ring
`target.valuationSubring`, the subtype of `L` given by
`target.valuation z ≤ 1`. The imported `valuationSubringAutOfUniqueExtension`
restricts the supplied field automorphism to this ring, with underlying
evaluation `σ (a : L)`. The subtraction and ideal membership in both
carrier clauses occur in this same ring.

The ideal at a real index has the definitional expansion

```lean
realRamificationIdeal target s =
  target.maximalIdeal ^ (Int.ceil (s + 1)).toNat
```

These are ordinary natural powers of the chosen ring's maximal ideal.
The real quantifiers have no lower bound; `Int.toNat` truncates
nonpositive ceilings to zero. The first clause retains the published
real ideal, and the second uses the ordinary power `n + 1`. The statement
imports only `LowerGroup`, whose existing import closure supplies the
actual subgroup, restricted automorphism, uniqueness predicate and real
ideal. The separate real-index property proof is not needed to formulate
this target.

## Original-to-adapted correspondence

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 370–469](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L370-L469).
The complete file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 1–470 were read directly, including the complete subgroup
definition, prerequisites and all six source proofs and the instance alias.

| Clause | Original declaration under `RamificationTheory.HilbertRamification.Higher` | Source signature lines |
| --- | --- | --- |
| 1 | M304.023, `mem_lowerRamificationGroup_iff` | 371–382 |
| 2 | M304.024, `mem_lowerRamificationGroup_nat_iff` | 385–393 |
| 3 | M304.025, `lowerRamificationGroup_antitone` | 398–402 |
| 4 | M304.026, `lowerRamificationGroup_normal` | 407–413 |
| 4 again, without another conjunct | M304.027, `lowerRamificationGroup.instNormal` | 441–448 |
| 5 | M304.028, `lowerRamificationGroup_neg_one` | 451–455 |
| 6 | M304.029, `lowerRamificationGroup_eq_top_of_le_neg_one` | 461–466 |

The shared telescope comes from lines 33 and 98–101, with the uniqueness
predicate at lines 48–52. The exponent and ideal are at lines 103–109 and
137–140, the restricted automorphism at lines 164–182, and the subgroup
at lines 304–368. All are reused by their published Lean names.

The conjunction and internal closure are an organizational adaptation of
these source conclusions, rather than a separately named theorem in the
literature. M304.027 is an instance alias for the normality theorem; it
adds no seventh mathematical conclusion. A later proof unit may prove
the six laws and install that alias against this published target.
The source partition records no patch10 modification for M304; its
conservative source-order edges add no hypotheses to this statement.

Intermediate-field base change M304.030–.036, normal filtration
structures, Herbrand functions and inverses, upper groups, host
comparisons and reciprocity are outside this statement.

## Attribution and modification record

Worker 1199 wrote the statement and this Markdown on 1 November 2026.
Worker 106 contributed the source extraction, six-clause grouping, exact
telescope and distinction between the normality conclusion and its
instance alias. Modifications prefix namespaces with `Langlands.NYLL`,
replace the source imports with the published `LowerGroup` module,
conjoin the six source conclusions in their source order, and move all
mathematical binders inside the proposition. The proofs and instance
implementation are omitted. All source mathematical data and
conclusions are preserved.

The registered original is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source is Apache-2.0. The existing
verbatim [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The supplement's ValuedFieldTheory attribution table and retained
NOTICE contain no `RealLowerGroups.lean` entry. Workspace, project and
supplied-Library errata directories were absent when checked.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
