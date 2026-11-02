# Elementary real lower ramification laws: proof

The module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupProof`
proves exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.LowerRamificationGroupPropertiesStatement.{u,v,w,x}`
by the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroupProperties`.
Its complete type is that proposition, with no mathematical parameters or
additional premises outside it. The module imports the unchanged
`LowerGroupStatement` and `RealIndexProof` modules. The former's import
closure supplies the published `LowerGroup` and `ValuationSubringAutProof`.

## Universes, telescope and actual objects

The four universe levels `u, v, w, x` are independent. The closed proposition
internally quantifies the complete telescope

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

The chosen value groups have universes `v` and `x`, independently of the
field carriers in `u` and `w`. The extension instance uses the algebra map
of the supplied `Algebra K L`. The last `x` in the uniqueness predicate
is its comparison-valuation universe. Each component theorem and the
instance alias quantify these same supplied data before their local arguments.
There is no finiteness, completeness, separability, `IsGalois`, preservation,
normality, filtration or endpoint premise.

For the proof explanation write `R = target.valuationSubring`,
`m = target.maximalIdeal`,
`G(s) = lowerRamificationGroup (base := base) (target := target) huniq s`,
and
`e(σ) = valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq σ`.
These abbreviate existing public objects. The ring `R` is the actual subtype
of `L` defined by `target.valuation a ≤ 1`. The map `e(σ) : R ≃+* R`
is the actual restriction of `σ : Gal(L/K) = (L ≃ₐ[K] L)`; its underlying
evaluation is `σ (a : L)`. Its inverse restricts `σ⁻¹`. Multiplication
of automorphisms applies the right factor first.

Every displacement and ideal membership is in this same ring `R`.
The ideal `m` is `IsLocalRing.maximalIdeal R`, and its powers are ordinary
natural ideal powers. The real ideal is definitionally

```lean
realRamificationIdeal target s =
  target.maximalIdeal ^ (Int.ceil (s + 1)).toNat
```

All real indices are allowed. Nonpositive ceilings truncate to zero,
and `m ^ 0 = ⊤`. No action or substitute subgroup is introduced.

## Implemented proofs and closed assembly

The right-associated conjunction has exactly six clauses in the following
order. The six component proofs retain the original source arguments.

1. `mem_lowerRamificationGroup_iff` states, for every real `s` and
   automorphism `σ`, that `σ ∈ G(s)` iff every `e(σ)(a) - a` lies in
   `realRamificationIdeal target s`. This is `Iff.rfl`, because it is
   precisely the carrier of the published subgroup.
2. `mem_lowerRamificationGroup_nat_iff` gives the carrier at every
   natural index `(n : ℝ)` using `m ^ (n + 1)`. The proof simplifies
   only with the real carrier theorem and the public
   `realRamificationIdeal_nat`. The quantifier includes `n = 0`.
3. `lowerRamificationGroup_antitone` introduces real indices `s ≤ t`,
   a member `σ ∈ G(t)` and `a : R`. The public
   `realRamificationIdeal_antitone` sends the displacement's membership
   at `t` to its membership at `s`, giving `G(t) ≤ G(s)`.
4. `lowerRamificationGroup_normal` constructs `Subgroup.Normal` by
   conjugation closure. Given `σ ∈ G(s)`, `τ : Gal(L/K)` and `a : R`,
   set `b = e(τ⁻¹)(a)`. Membership of `σ` gives
   `e(σ)(b) - b ∈ realRamificationIdeal target s`. The public theorem
   `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`
   sends this element into the same ideal under `e(τ)`. The identity

   ```text
   e(τ * σ * τ⁻¹)(a) - a = e(τ)(e(σ)(b) - b)
   ```

   follows by simplifying with the public composition and inverse
   evaluation laws and `map_sub`. Rewriting the goal by this identity
   gives the transported membership, proving normality for every real `s`.
5. `lowerRamificationGroup_neg_one` uses subgroup extensionality,
   the real carrier theorem, and `realRamificationIdeal_neg_one`.
   Every displacement belongs to the top ideal, so `G(-1) = ⊤`.
6. `lowerRamificationGroup_eq_top_of_le_neg_one` has implicit `{s : ℝ}`
   and explicit `hs : s ≤ -1`. Subgroup extensionality and the carrier
   theorem reduce the equality to ideal membership. Simplification with
   `realRamificationIdeal_eq_top_of_le_neg_one hs` proves `G(s) = ⊤`.

The source instance `lowerRamificationGroup.instNormal` is retained as a
direct alias of `lowerRamificationGroup_normal` for the same `base`,
`target`, supplied extension instance, `huniq` and real `s`. It registers
the proved normality law and adds no seventh target conjunct.

The section carrying mathematical parameters ends before the final theorem.
`lowerRamificationGroupProperties` introduces the target's complete internal
telescope and assembles the six component proofs in the exact published
order, specializing each to the same supplied data. This assembly is an
internal organizational theorem derived from these six proofs; the original
literature does not give a separate name to the closed conjunction.

## Original-to-adapted declaration map

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 370–469](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L370-L469).
Its complete-file SHA-256 is
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 1–470 were read directly, including the shared telescope, actual
objects, subgroup structure and all seven declarations below.

Each original name is in
`RamificationTheory.HilbertRamification.Higher`; each adapted name is
in `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`
with the same short name.

| Unit | Original and adapted short name | Source signature | Source proof or value |
| --- | --- | --- | --- |
| M304.023 | `mem_lowerRamificationGroup_iff` | 371–381 | 382 |
| M304.024 | `mem_lowerRamificationGroup_nat_iff` | 385–394 | 394–395 |
| M304.025 | `lowerRamificationGroup_antitone` | 398–402 | 402–404 |
| M304.026 | `lowerRamificationGroup_normal` | 407–412 | 412–438 |
| M304.027 | `lowerRamificationGroup.instNormal` | 441–446 | 447–448 |
| M304.028 | `lowerRamificationGroup_neg_one` | 451–455 | 455–457 |
| M304.029 | `lowerRamificationGroup_eq_top_of_le_neg_one` | 461–466 | 466–469 |

The source universe/telescope is at lines 33 and 98–101; uniqueness is at
48–52; the exponent and ideal are at 103–109 and 137–140; the actual
restricted automorphism is at 164–182; and the subgroup is at 304–368.
Their published counterparts and the real-index and automorphism
property proofs are reused by Lean name, unchanged. The source partition
`notes/reuse/nyll-public-port/m289-m312.md` records no patch10 change for
M304. Its source-order planning edges introduce no mathematical hypotheses.

## Attribution and modifications

Worker 1199 adapted the proof and wrote this companion on 1 November 2026.
Worker 106 contributed source extraction, six-clause exact-target and
parameter analysis, and the proof route. The adaptation retains the
source's six proofs, normality instance alias, short names, hypotheses
and simplifier attributes. It prefixes namespaces with `Langlands.NYLL`,
replaces the whole-file source imports with the published statement
and real-index proof, omits unused pointwise scope, universe `y` and
noncomputable section, and adds the closed conjunction assembly. The
published statement and every imported Lean/Markdown pair remain unchanged.

The registered original is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md`
and the retained original NOTICE have no `RealLowerGroups.lean` entry.
The workspace, project and supplied-Library errata directories were absent
at preparation.

The original header is preserved: copyright 2026 Naganori Yamaguchi,
all rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged,
including inherited notices. The Lean header records the modifications.
The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from upstream's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

This unit proves these six laws and supplies their normality instance alias.
Intermediate-field base change M304.030–.036, normal filtration structures,
Herbrand and inverse functions, upper groups, host inertia and reciprocity
remain separate work.
