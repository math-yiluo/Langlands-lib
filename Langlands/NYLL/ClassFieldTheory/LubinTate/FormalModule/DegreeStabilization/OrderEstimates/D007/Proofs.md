# NYLL M351.007: proof of the order of a finite sum

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D007.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d007Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d007`, with universe
parameters `u, v, w`. The theorem takes the source binders of M351.007 in
source order and kinds, with the source hypothesis names, and its type is
`d007Statement` applied to all of them. Hence it is used exactly like the
source theorem.

## Statement proved

For an arbitrary commutative ring `R`, an arbitrary type of variables `τ`
(and, where present, an arbitrary index type `ι` and finite set `s : Finset ι`),
with Mathlib's total order `MvPowerSeries.order : MvPowerSeries τ R → ℕ∞`:
if `m ≤ (f i).order` for all `i ∈ s`, then `m ≤ (∑ i ∈ s, f i).order`, for every `m : ℕ∞`. The exact Lean statement is the target's body; see the target's
paired Markdown `Statements.md`.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.le_order_finset_sum_stabilization`: signature lines 215–219,
proof lines 220–231
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

After `unfold d007Statement`, induct on `s` with `Finset.induction_on` (classical
decidable equality). For `s = ∅` the sum is `0`, of order `⊤`
(`MvPowerSeries.order_zero`), and `le_top` closes the goal. For `insert i s` with
`i ∉ s`, `Finset.sum_insert` splits off `f i`; the hypothesis at `i` and the
induction hypothesis (applied to the restricted hypothesis) give `m` below the
minimum of the two orders, and `MvPowerSeries.min_order_le_add` bounds that
minimum by the order of the sum.

## Changes from the source proof

The source proof is used verbatim after the added `unfold d007Statement`.

## Imports

The module imports the target module only. The source module's imports
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
