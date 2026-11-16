# NYLL M351.010: proof of the order of a difference of two products of powers

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D010.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d010Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d010`, with universe
parameters `u, v, w`. The theorem takes the source binders of M351.010 in
source order and kinds, with the source hypothesis names, and its type is
`d010Statement` applied to all of them. Hence it is used exactly like the
source theorem.

## Statement proved

For an arbitrary commutative ring `R`, arbitrary types `τ` and `ι`,
and a finite set `s : Finset ι`,
with Mathlib's total order `MvPowerSeries.order : MvPowerSeries τ R → ℕ∞`:
if for every `i ∈ s` the exponent `n i` is nonzero, `f i` and `g i` have order at least one and `f i - g i` has order at least two, then `(((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤ ((∏ i ∈ s, f i ^ n i) - ∏ i ∈ s, g i ^ n i).order`. The exact Lean statement is the target's body; see the target's
paired Markdown `Statements.md`.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization`: signature lines 297–307,
proof lines 308–398
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

After `unfold d010Statement`, three local lemmas replace the source's calls of
the private theorems M351.006, M351.008 and M351.009.

- `hpow`: M351.006 for an arbitrary series and exponent, by the source proof of
  M351.006.
- `hprod`: M351.008 for the given `f`, `n` and an arbitrary finite set `t`:
  if every `f j` with `j ∈ t` has order at least one, then
  `((∑ j ∈ t, n j : ℕ) : ℕ∞) ≤ (∏ j ∈ t, f j ^ n j).order`. Proof: the cast of
  the sum is the sum of the casts (`Nat.cast_sum`), each summand is bounded by
  `(f j ^ n j).order` (`Finset.sum_le_sum` with `hpow`), and Mathlib's
  `MvPowerSeries.le_order_prod` bounds the sum of the orders by the order of
  the product.
- `hpowSub`: M351.009 for arbitrary series `a`, `b` of order at least one and
  exponent `k`, by the source proof of M351.009, in which the bound
  `(k - 1 : ℕ) ≤ (∑ i ∈ range k, a ^ i * b ^ (k - 1 - i)).order` is proved
  coefficientwise (`MvPowerSeries.le_order`, `map_sum`,
  `MvPowerSeries.coeff_of_lt_order`) instead of through M351.007.

Then the source induction on `s` (`Finset.induction_on`, classical decidable
equality) follows. For `s = ∅` both products are `1`, their difference is `0`
of order `⊤`, and `le_top` closes the goal. For `insert i s` with `i ∉ s`:

- `hni : n i ≠ 0` from `hn`;
- `hpowDifference`: `n i + 1 ≤ (f i ^ n i - g i ^ n i).order`, since
  `n i + 1 = 2 + (n i - 1)` (`norm_cast`, `omega`, using `hni`),
  `2 ≤ (f i - g i).order` (`hfg`) and `hpowSub`;
- `hprodF`: `∑ j ∈ s, n j ≤ (∏ j ∈ s, f j ^ n j).order` by `hprod`;
- `hpowG`: `n i ≤ (g i ^ n i).order` by `hpow`;
- `hprodDifference`: the induction hypothesis for `s`, applied to the
  restricted hypotheses;
- `hleft` and `hright`: the bound `(n i + ∑ j ∈ s, n j) + 1` for the orders of
  `(f i ^ n i - g i ^ n i) * ∏ j ∈ s, f j ^ n j` and of
  `g i ^ n i * (∏ j ∈ s, f j ^ n j - ∏ j ∈ s, g j ^ n j)`, each by splitting the
  cast (`norm_cast`, `omega`), adding the two bounds above and
  `MvPowerSeries.le_order_mul`.

After `Finset.sum_insert` and `Finset.prod_insert`, the difference of products
is rewritten by `ring` as the sum of these two products, and `le_min` with
`MvPowerSeries.min_order_le_add` concludes.

## Changes from the source proof

The source proof is used after the added `unfold d010Statement`, with its calls
of the private theorems M351.006, M351.008 and M351.009 replaced by the local
lemmas `hpow`, `hprod` and `hpowSub` above (`hprod` is proved from
`MvPowerSeries.le_order_prod` rather than by the source's induction for
M351.008). The proof therefore does not import the separately routed proofs of
M351.006, M351.008 and M351.009 and has no dependency on another proof task.

## Imports

The module imports the target module, `Mathlib.Algebra.Ring.GeomSum` (for `Commute.mul_geom_sum₂`) and `Mathlib.Tactic.Ring` (for `ring`). The source module's imports
(`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`,
`Mathlib.RingTheory.MvPowerSeries.Trunc`) are not needed; the target module
imports `Mathlib.RingTheory.MvPowerSeries.Order`.

## Checks

With environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) the module compiles without
errors or warnings; the theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## License

The Lean file keeps the original copyright, Apache-2.0 license and author
header and records the modifications. The original `LICENSE` and `NOTICE` are
in the Library at `licenses/NYLL/`.

## Port preparation

Worker 489 supplied the complete shared proof draft. Worker 277 checked the
source correspondence, preserved the proof and original header, clarified
the statement description and prepared this pair for validation and
independent review on 16 November 2026.
