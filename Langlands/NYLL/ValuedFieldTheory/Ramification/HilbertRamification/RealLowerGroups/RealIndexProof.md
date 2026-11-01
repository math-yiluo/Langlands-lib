# Real-index exponent and ideal properties: proof

This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.realRamificationIndexProperties`.
Its complete type is the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.RealRamificationIndexPropertiesStatement.{w, x}`,
imported from
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndexStatement`.
The theorem has no declaration parameters and no hypotheses outside that
proposition. The module also imports `Mathlib.Tactic.Linarith` for the
`linarith` calls of the original proofs.

The proposition conjoins the elementary property theorems M304.005–.008 and
M304.010–.013. Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 111–162](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L111-L162),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, states and proves these
eight theorems. The complete source file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
The exponent theorems occupy lines 111–135 and the ideal theorems lines
142–162, including their docstrings. Lines 1–165 of the file were read for
this adaptation.

## Exact target and universes

In the namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`,
the target expands to:

```lean
Monotone realRamificationExponent ∧
realRamificationExponent (-1) = 0 ∧
(∀ {s : ℝ}, s ≤ -1 → realRamificationExponent s = 0) ∧
(∀ n : ℕ, realRamificationExponent (n : ℝ) = n + 1) ∧
(∀ {L : Type w} [Field L]
    (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L),
  (∀ {s t : ℝ}, s ≤ t → realRamificationIdeal target t ≤ realRamificationIdeal target s) ∧
  realRamificationIdeal target (-1) = ⊤ ∧
  (∀ n : ℕ, realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1)) ∧
  (∀ {s : ℝ}, s ≤ -1 → realRamificationIdeal target s = ⊤))
```

The published definitions are used unchanged:
`realRamificationExponent s = (Int.ceil (s + 1)).toNat`, and
`realRamificationIdeal target s` is the power
`target.maximalIdeal ^ realRamificationExponent s` in
`Ideal target.valuationSubring`. Here `target.maximalIdeal` is the actual
maximal ideal of the chosen valuation ring `target.valuationSubring`.

The theorem is declared as `realRamificationIndexProperties :
RealRamificationIndexPropertiesStatement.{w, x}` with the module's universe
variables `w` and `x`. Its level parameters are exactly `[w, x]`, in that
order, and they remain independent. `w` is the universe of the field carrier
`L` in the ideal clauses. `x` is the universe of the chosen value group of
`target`. Neither level is fixed to `0`. The four exponent clauses involve no
universe. The proof supplies the four ideal facts for an arbitrary field `L`
of `Type w` and arbitrary chosen `target : DVF.{w, x} L`. It uses no base
field, algebra, valuation extension, uniqueness, completeness, separability,
finite-dimensionality, Galois, automorphism or filtration hypothesis.

## Implemented proof

The module first proves the eight original theorems under their original short
names, and then assembles them. In the namespace above, the section variables
are `{L : Type w} [Field L]` and an implicit `{target : DVF.{w, x} L}`. As in
the original, Lean includes these only in the ideal theorems, because only
those mention `target`.

1. `realRamificationExponent_mono : Monotone realRamificationExponent`.
   Given `s ≤ t`, apply `Int.toNat_le_toNat` and then `Int.ceil_mono`. The
   remaining goal `s + 1 ≤ t + 1` follows by `linarith`.
2. `realRamificationExponent_neg_one : realRamificationExponent (-1) = 0`,
   tagged `@[simp]`. `simp` unfolds the exponent; `-1 + 1 = 0`, the ceiling
   of `0` is `0`, and `Int.toNat 0 = 0`.
3. `realRamificationExponent_eq_zero_of_le_neg_one`: for `s ≤ -1` the exponent
   is `0`. Rewriting with the definition and `Int.toNat_eq_zero` reduces the
   goal to `Int.ceil (s + 1) ≤ 0`. `linarith` gives `s + 1 ≤ 0`, and
   `Int.ceil_le` turns this into the goal, after `simpa` identifies the cast
   `((0 : ℤ) : ℝ)` with `0`.
4. `realRamificationExponent_nat`, tagged `@[simp]`: for `n : ℕ`,
   `realRamificationExponent (n : ℝ) = n + 1`. `simp` unfolds the exponent and
   evaluates the ceiling of the natural number `n + 1` and its `Int.toNat`.
5. `realRamificationIdeal_antitone`: for `s ≤ t`, the ideal at `t` is contained
   in the ideal at `s`. By theorem 1 the exponent at `s` is at most the
   exponent at `t`. `Ideal.pow_le_pow_right` then gives
   `target.maximalIdeal ^ realRamificationExponent t ≤
   target.maximalIdeal ^ realRamificationExponent s`, which is the claim by
   definition. This is the original proof term.
6. `realRamificationIdeal_neg_one`, tagged `@[simp]`: the ideal at `-1` is `⊤`.
   Unfold the ideal and rewrite with theorem 2, `pow_zero` and
   `Ideal.one_eq_top`.
7. `realRamificationIdeal_nat`, tagged `@[simp]`: for `n : ℕ`, the ideal at
   `(n : ℝ)` is `target.maximalIdeal ^ (n + 1)`. Unfold the ideal and rewrite
   with theorem 4.
8. `realRamificationIdeal_eq_top_of_le_neg_one`: for `s ≤ -1` the ideal is `⊤`.
   Unfold the ideal and rewrite with theorem 3 at the hypothesis `s ≤ -1`, then
   with `pow_zero` and `Ideal.one_eq_top`.

The closed theorem is the anonymous-constructor term

```lean
⟨realRamificationExponent_mono, realRamificationExponent_neg_one,
  realRamificationExponent_eq_zero_of_le_neg_one, realRamificationExponent_nat,
  fun _ => ⟨realRamificationIdeal_antitone, realRamificationIdeal_neg_one,
    realRamificationIdeal_nat, realRamificationIdeal_eq_top_of_le_neg_one⟩⟩
```

The first four components are theorems 1–4, the first four conjuncts of the
target. For the fifth conjunct, the implicit `L` and the instance `[Field L]`
are introduced automatically, and `fun _` binds the explicit `target`. The
inner tuple supplies theorems 5–8 at that `L` and `target`. The implicit
`target` argument of each ideal theorem is then determined by the expected
type. Theorems 3, 5 and 8 take their real indices as implicit arguments and
their order hypotheses as explicit ones. This matches the binders of the
corresponding clauses `∀ {s : ℝ}, s ≤ -1 → …` and
`∀ {s t : ℝ}, s ≤ t → …`. Theorems 4 and 7 take `n : ℕ` explicitly, as their
clauses do.

None of the eight theorems takes another clause of the target as a hypothesis.
Theorems 5–8 use only the exponent theorems 1–4 proved before them in this
module. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Module contents

The module adds the closed theorem `realRamificationIndexProperties` and the
eight original-name theorems listed above. The four `@[simp]` attributes are
those of the original. The rewrites with the definitions also generate
Lean's standard equation theorems `realRamificationExponent.eq_1` and
`realRamificationIdeal.eq_1`, which restate the published definition bodies.
The module adds no definition, instance, axiom or other target. It changes
neither the published definitions nor the published statement, and no
imported Lean/Markdown pair is edited.

## Original correspondence

All original names are in the source namespace
`RamificationTheory.HilbertRamification.Higher`, opened at lines 91–92. Each
adapted theorem has the same short name in
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`. A docstring
precedes each signature.

| Item | Original and adapted name | Signature lines | Original proof lines | Implemented proof |
| --- | --- | --- | --- | --- |
| M304.005 | `realRamificationExponent_mono` | 112–113 | 114–117 | Same tactic proof. |
| M304.006 | `realRamificationExponent_neg_one` | 120–121 | 122 | Same `simp` proof. |
| M304.007 | `realRamificationExponent_eq_zero_of_le_neg_one` | 125–127 | 128–130 | Same tactic proof. |
| M304.008 | `realRamificationExponent_nat` | 133–134 | 135 | Same `simp` proof. |
| M304.010 | `realRamificationIdeal_antitone` | 143–144 | 145 | Same term, without the `by exact` wrapper. |
| M304.011 | `realRamificationIdeal_neg_one` | 148–149 | 150 | `rw` with M304.006, `pow_zero` and `Ideal.one_eq_top` instead of `simp [realRamificationIdeal]`. |
| M304.012 | `realRamificationIdeal_nat` | 153–154 | 155 | `rw` with M304.008 instead of `simp [realRamificationIdeal]`. |
| M304.013 | `realRamificationIdeal_eq_top_of_le_neg_one` | 158–160 | 161–162 | `rw` with M304.007, `pow_zero` and `Ideal.one_eq_top` instead of the original `simp` call with the same lemma. |

The original `simp` proofs of M304.011–.013 rely on the `@[simp]` exponent
theorems and on simp's simplification of `m ^ 0` to `⊤`. The implemented
rewrites make those steps explicit. The signatures are unchanged apart from the
namespace prefix. The source section at lines 98–101 also declares a base
field `K`, `[Algebra K L]`, a base `DVF` and a `HasExtension` instance. No
signature among the eight mentions them, so Lean does not include them, and
this module omits them. The original data definitions at lines 103–109 and
137–140 are the published `RealIndex` definitions, imported rather than
restated. The source partition `notes/reuse/nyll-public-port/m289-m312.md`
maps M304.005–.008 and M304.010–.013 to exactly these adapted names and
records no patch10 change for M304. No errata directories exist in the
project, workspace or current Library.

## Attribution and modifications

Worker 1045 wrote this adaptation and its explanation on 1 November 2026.
Worker 106 contributed the source extraction, grouping of the eight properties
and parameter analysis in the task contract. The adaptation keeps the original
theorems, names, signatures and proof route. It prefixes the namespace with
`Langlands.NYLL` and imports the published statement module instead of the
upstream imports. It omits the unused section parameters, the noncomputable
section and the pointwise scope. The original docstrings, which read
"States the theorem …", are replaced by descriptive ones. Three ideal proofs
rewrite with the exponent theorems instead of calling `simp`. Finally the
closed theorem `realRamificationIndexProperties` conjoins the eight theorems.
The source hypotheses and conclusions are unchanged.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source path
above. Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
supplement's `files/Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` has no
entry for `RealLowerGroups.lean`.

The original copyright and author header is retained in the Lean file:
copyright 2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all
rights reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The
source is released under Apache-2.0. The existing copies of
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, including the
inherited notices and earlier-source credits. The Lean header records the
modifications.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. This unit proves the intrinsic
real-index properties only. Valuation-ring automorphisms and their properties
and the lower and upper ramification filtrations are separate units.
