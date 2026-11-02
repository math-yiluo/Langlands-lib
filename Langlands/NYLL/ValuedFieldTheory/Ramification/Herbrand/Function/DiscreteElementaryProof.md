# Elementary slope and natural-sum laws of the Herbrand function: proof

This module proves
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandDiscreteElementary`.
Its complete type is the published closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.HerbrandDiscreteElementaryStatement.{u}`,
imported from
[`DiscreteElementaryStatement`](DiscreteElementaryStatement.md). The theorem
has no declaration parameters and no hypotheses outside that proposition.
The module also imports `Mathlib.Algebra.Order.BigOperators.Group.Finset`,
which declares `Finset.sum_nonneg` and `Finset.sum_le_sum`, and
`Mathlib.SetTheory.Cardinal.NatCard`, which declares `Finite.card_pos`.

The proposition conjoins the elementary theorems M303.005–.012. Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`, lines 55–109](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean#L55-L109),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, states and proves these
eight theorems. The complete source file has SHA-256
`668006f8122da36b9bd34657988f9d0d6164a629ea10feb340002f2317c40580`.
Lines 1–130 of the file were read for this adaptation.

## Exact target and universes

In the namespace
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`,
the target expands to:

```lean
(∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G),
  herbrandValueNat F 0 = 0 ∧
  ∀ n : ℕ, herbrandValueNat F (n + 1) = herbrandValueNat F n + herbrandSlope F n) ∧
(∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
  (∀ i : ℕ, 0 < herbrandSlope F i) ∧
  (∀ i : ℕ, 0 ≤ herbrandSlope F i) ∧
  (∀ i : ℕ, (1 : ℝ) / Nat.card (F.lower 0) ≤ herbrandSlope F i) ∧
  (∀ n : ℕ, 0 ≤ herbrandValueNat F n) ∧
  (∀ n : ℕ, (n : ℝ) / Nat.card (F.lower 0) ≤ herbrandValueNat F n) ∧
  StrictMono (herbrandValueNat F))
```

The published [`Definitions`](Definitions.md) are used unchanged:
`herbrandSlope F i` is the real quotient
`(Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)`, and
`herbrandValueNat F n` is the finite sum
`∑ i ∈ Finset.range n, herbrandSlope F i` of the slopes at `i < n`.

The theorem is declared as
`herbrandDiscreteElementary : HerbrandDiscreteElementaryStatement.{u}` with
the module's universe variable `u`. Its only level parameter is `u`, which is
not fixed. In both blocks the group carrier `G` is an arbitrary type in
universe `u`. The first block uses no finiteness hypothesis. The second block
uses exactly the `[Finite G]` binder of the target. The proof uses no
enumeration, eventual-triviality cutoff, valuation, extension or Galois
hypothesis.

## Implemented proof

The module first proves the eight original theorems under their original
short names, and then assembles them. In the namespace above, a section
declares `variable {G : Type u} [Group G] [Finite G]` and
`variable (F : AntitoneNormalSubgroupFiltration G)`, as the original does at
lines 36–37. As in the original, theorems 1 and 2 are preceded by
`omit [Finite G] in`, so their signatures have no finiteness hypothesis.
Theorems 3–8 include `[Finite G]`.

1. `herbrandValueNat_zero : herbrandValueNat F 0 = 0`, tagged `@[simp]`.
   `simp [herbrandValueNat]` unfolds the definition; the sum over the empty
   range `Finset.range 0` is `0`.
2. `herbrandValueNat_succ (n : ℕ)`: the sum at `n + 1` is the sum at `n` plus
   `herbrandSlope F n`. `simp [herbrandValueNat, Finset.sum_range_succ]`
   unfolds the definition and splits off the last term of the range sum.
3. `herbrandSlope_pos (i : ℕ) : 0 < herbrandSlope F i`. `Finite.card_pos`
   gives `0 < Nat.card (F.lower (i + 1))` and `0 < Nat.card (F.lower 0)`.
   Its instance arguments are found by Mathlib's instance search:
   `Subtype.finite` shows that the subgroup carrier of the finite group `G` is
   finite, and `One.instNonempty` with the subgroup's `1` shows that it is
   nonempty. `Nat.cast_pos` transfers both inequalities to `ℝ`, and `div_pos`
   gives positivity of the quotient.
4. `herbrandSlope_nonneg (i : ℕ) : 0 ≤ herbrandSlope F i` is the weakening
   `(herbrandSlope_pos F i).le` of theorem 3.
5. `one_div_card_le_herbrandSlope (i : ℕ)`:
   `(1 : ℝ) / Nat.card (F.lower 0) ≤ herbrandSlope F i`. After rewriting with
   the definition of `herbrandSlope`, both sides are quotients by
   `Nat.card (F.lower 0)`, which is positive in `ℝ` by `Finite.card_pos` and
   `exact_mod_cast`. `div_le_div_iff_of_pos_right` reduces the goal to
   `1 ≤ (Nat.card (F.lower (i + 1)) : ℝ)`. `exact_mod_cast` closes it from
   `0 < Nat.card (F.lower (i + 1))`, given by `Finite.card_pos`; in `ℕ` this
   is the inequality `1 ≤ Nat.card (F.lower (i + 1))`.
6. `herbrandValueNat_nonneg (n : ℕ) : 0 ≤ herbrandValueNat F n`.
   `Finset.sum_nonneg` applies theorem 4 to every term of the sum.
7. `nat_div_card_le_herbrandValueNat (n : ℕ)`:
   `(n : ℝ) / Nat.card (F.lower 0) ≤ herbrandValueNat F n`. After rewriting
   with the definition of `herbrandValueNat`, a `calc` chain first writes the
   left side as the sum of `n` copies of `(1 : ℝ) / Nat.card (F.lower 0)`
   over `Finset.range n`, by `simp [div_eq_mul_inv]`. `Finset.sum_le_sum`
   then compares this sum termwise with the sum of the slopes, using
   theorem 5.
8. `herbrandValueNat_strictMono : StrictMono (herbrandValueNat F)`.
   `strictMono_nat_of_lt_succ` reduces strict monotonicity on `ℕ` to
   `herbrandValueNat F n < herbrandValueNat F (n + 1)` for every `n`. Rewriting
   with theorem 2 turns this into
   `herbrandValueNat F n < herbrandValueNat F n + herbrandSlope F n`, which
   `lt_add_of_pos_right` proves from theorem 3.

The closed theorem is the anonymous-constructor term

```lean
⟨fun F => ⟨herbrandValueNat_zero F, herbrandValueNat_succ F⟩,
  fun F => ⟨herbrandSlope_pos F, herbrandSlope_nonneg F,
    one_div_card_le_herbrandSlope F, herbrandValueNat_nonneg F,
    nat_div_card_le_herbrandValueNat F, herbrandValueNat_strictMono F⟩⟩
```

In each block, the implicit `G` and the instance binders of the target are
introduced automatically, and `fun F` binds the explicit filtration. The
first block applies theorems 1 and 2 at that `F`. The second block applies
theorems 3–8 at that `F`, and their `[Finite G]` argument is the block's own
instance binder. Theorems 2–7 take their index `n` or `i` as an explicit
argument, so applying them to `F` gives exactly the conjuncts
`∀ n : ℕ, …` and `∀ i : ℕ, …` of the target. Theorems 1 and 8 have no index
argument, as their conjuncts have none.

None of the eight theorems takes a clause of the target as a hypothesis.
Theorems 4–8 use only theorems proved before them in this module. The proof
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Module contents

The module adds the closed theorem `herbrandDiscreteElementary` and the eight
original-name theorems listed above. The `@[simp]` attribute on
`herbrandValueNat_zero` is that of the original. Rewriting and simplifying
with the definitions also generates Lean's standard equation theorems
`herbrandSlope.eq_1` and `herbrandValueNat.eq_1`, which restate the published
definition bodies. The module adds no definition, instance, axiom or other
target. It changes neither the published definitions nor the published
statement, and no imported Lean/Markdown pair is edited.

## Original correspondence

All original names are in the source namespace
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`,
opened at lines 33–34. Each adapted theorem has the same short name in
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`.
The source partition `notes/reuse/nyll-public-port/m289-m312.md` maps
M303.005–.012 to exactly these adapted names.

| Item | Original and adapted name | Signature lines | Original proof lines | Implemented proof |
| --- | --- | --- | --- | --- |
| M303.005 | `herbrandValueNat_zero` | 57 | 58 | Same `simp` proof, with `omit [Finite G] in` and `@[simp]`. |
| M303.006 | `herbrandValueNat_succ` | 62–64 | 65 | Same `simp` proof, with `omit [Finite G] in`. |
| M303.007 | `herbrandSlope_pos` | 68–69 | 70–72 | Same tactic proof. |
| M303.008 | `herbrandSlope_nonneg` | 75–76 | 77 | Same term. |
| M303.009 | `one_div_card_le_herbrandSlope` | 80–81 | 82–86 | Same tactic proof. |
| M303.010 | `herbrandValueNat_nonneg` | 89–90 | 91 | Same tactic proof. |
| M303.011 | `nat_div_card_le_herbrandValueNat` | 94–95 | 96–102 | Same `calc` proof. |
| M303.012 | `herbrandValueNat_strictMono` | 105 | 106–109 | Same tactic proof. |

Apart from the docstrings and the namespace prefix, the signatures and proofs
are character-for-character those of lines 55–109. The original data
definitions at lines 46–53 are the published `Definitions`, imported rather
than restated. The original local instances M303.001–.002 at lines 39–44
provide `Fintype` and membership decidability for subgroups. This module
omits them: no signature mentions them, and the proofs compile without them,
because `Finite.card_pos` needs only the `Finite` and `Nonempty` instances
named in theorem 3. The source partition records no patch10 change for M303.
No applicable errata were found in the project, workspace or current Library.

## Attribution and modifications

Worker 1045 wrote this adaptation and its explanation on 2 November 2026.
Worker 106 contributed the source extraction, grouping of the eight laws and
the scope analysis in the task contract. The adaptation keeps the original
theorems, names, signatures, `omit` commands, `@[simp]` attribute and proofs.
It prefixes the namespace with `Langlands.NYLL` and imports the published
statement module and the two Mathlib modules above instead of the upstream
imports. It omits the local subgroup instances and the noncomputable section,
and places the eight theorems in a section named `Laws`. The original
docstrings, which read "States the theorem …", are replaced by descriptive
ones. Finally the closed theorem `herbrandDiscreteElementary` conjoins the
eight theorems. The source hypotheses and conclusions are unchanged.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` has no
entry for `Function.lean`.

The original copyright and author header is retained in the Lean file:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, including
the inherited notices and earlier-source credits. The Lean header records the
modifications.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. This unit proves the elementary
slope and natural-sum laws only. The piecewise-linear `herbrandFunction`, its
evaluation, finite, basic and analytic laws are separate units.
