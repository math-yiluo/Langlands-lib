# NYLL M351.009: proof of the order of a difference of two powers

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D009.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d009Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d009`, with universe
parameters `u, v`. The theorem takes the source binders of M351.009 in
source order and kinds, with the source hypothesis names, and its type is
`d009Statement` applied to all of them. Hence it is used exactly like the
source theorem.

## Statement proved

For an arbitrary commutative ring `R` and an arbitrary type of variables `τ`,
with Mathlib's total order `MvPowerSeries.order : MvPowerSeries τ R → ℕ∞`:
if `(1 : ℕ∞) ≤ f.order` and `(1 : ℕ∞) ≤ g.order`, then `(f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤ (f ^ n - g ^ n).order` for every natural `n` (truncated subtraction `n - 1`). The exact Lean statement is the target's body; see the target's
paired Markdown `Statements.md`. The argument includes `n = 0`: the geometric
sum is empty, the difference of zeroth powers is zero and its order is `⊤`.
It also applies when `f = g`, when both sides of the order inequality are `⊤`.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.order_sub_add_pred_le_order_pow_sub_pow_stabilization`: signature lines 259–266,
proof lines 267–295
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

After `unfold d009Statement`, two local lemmas are proved.

- `hpow`: M351.006 for an arbitrary series and exponent, by the source proof of
  M351.006.
- `hsum`: for a finite set `t` of naturals and `F : ℕ → MvPowerSeries τ R`, a
  common bound `m ≤ (F i).order` on `t` bounds `(∑ i ∈ t, F i).order`. It is
  proved coefficientwise: by `MvPowerSeries.le_order` it suffices that every
  coefficient of total degree below `m` vanishes; `map_sum` writes that
  coefficient of the sum as the sum of coefficients, each of which vanishes by
  `MvPowerSeries.coeff_of_lt_order` since its degree is below `m ≤ (F i).order`.

Then the source argument follows. Let `q = ∑ i ∈ range n, f ^ i * g ^ (n - 1 - i)`.
By `hsum`, `(n - 1 : ℕ) ≤ q.order` follows from the bound for each summand: for
`i < n`, `n - 1 = i + (n - 1 - i)` (`norm_cast`, `omega`), and `hpow` for `f`
and `g` with `MvPowerSeries.le_order_mul` gives
`i + (n - 1 - i) ≤ (f ^ i * g ^ (n - 1 - i)).order`. The factorization
`(f - g) * q = f ^ n - g ^ n` is `(Commute.all f g).mul_geom_sum₂ n`. Finally,
`(f - g).order + (n - 1) ≤ (f - g).order + q.order` (`add_le_add_right`),
`≤ ((f - g) * q).order` (`MvPowerSeries.le_order_mul`), which equals
`(f ^ n - g ^ n).order` by the factorization.

## Changes from the source proof

The source proof is used after the added `unfold d009Statement`, with its calls
of the private M351.006 theorem replaced by the local lemma `hpow` and its use
of the private M351.007 theorem (`apply le_order_finset_sum_stabilization`)
replaced by `apply hsum`. `hsum` is proved by a coefficientwise argument rather
than by the source's induction for M351.007. The proof therefore does not import
the separately routed proofs of M351.006 and M351.007 and has no dependency on
another proof task.

## Imports

The module imports the target module and `Mathlib.Algebra.Ring.GeomSum` (for `Commute.mul_geom_sum₂`). The source module's imports
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
