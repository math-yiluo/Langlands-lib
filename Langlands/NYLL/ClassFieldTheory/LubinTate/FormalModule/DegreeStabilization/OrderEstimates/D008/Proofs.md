# NYLL M351.008: proof of the order of a finite product of powers

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D008.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d008Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d008`, with universe
parameters `u, v, w`. The theorem takes the source binders of M351.008 in
source order and kinds, with the source hypothesis names, and its type is
`d008Statement f n hf`. The ring `R`, variable type `τ`, index type `ι`
and finite set `s` are implicit; the functions `f`, `n` and the hypothesis
`hf` are explicit, in that order. Hence it is used exactly like the source
theorem. Worker 187 adopted Worker 489's shared proof draft for Task 6731.

## Statement proved

For an arbitrary commutative ring `R`, an arbitrary type of variables `τ`,
an arbitrary index type `ι` and a finite set `s : Finset ι`,
with Mathlib's total order `MvPowerSeries.order : MvPowerSeries τ R → ℕ∞`:
if `(1 : ℕ∞) ≤ (f i).order` for all `i ∈ s`, then `((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, f i ^ n i).order`. The exact Lean statement is the target's body; see the target's
paired Markdown `Statements.md`.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.natCast_sum_le_order_finset_prod_pow_stabilization`: signature lines 233–238,
proof lines 239–257
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

After `unfold d008Statement`, a local lemma `hpow` states M351.006 for an
arbitrary series `h` and exponent `k` (`1 ≤ h.order → (k : ℕ∞) ≤ (h ^ k).order`)
and is proved by the source proof of M351.006 (the `calc` through `k • 1` and
`MvPowerSeries.le_order_pow`). Then induct on `s` with `Finset.induction_on`.
For `s = ∅` the cast of the empty sum is `0` and `bot_le` closes the goal. For
`insert i s`, `Finset.sum_insert` and `Finset.prod_insert` split off the index
`i`; `norm_cast` splits the cast of the sum; `hpow` at `f i`, `n i` and the
induction hypothesis bound the two summands by the orders of `f i ^ n i` and of
the remaining product; `MvPowerSeries.le_order_mul` bounds the sum of these
orders by the order of the product.

## Changes from the source proof

The source proof is used after the added `unfold d008Statement`, with its call
of the private M351.006 theorem replaced by the local lemma `hpow`. The proof
therefore does not import the separately routed proof of M351.006 and has no
dependency on another proof task.

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
