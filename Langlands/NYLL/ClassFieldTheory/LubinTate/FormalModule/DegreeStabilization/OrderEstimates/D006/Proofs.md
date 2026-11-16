# NYLL M351.006: proof of the order of a power

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D006.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d006Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d006`, with universe
parameters `u, v`. The theorem takes the source binders of M351.006 in
source order and kinds, with the source hypothesis names, and its type is
`d006Statement` applied to all of them. Hence it is used exactly like the
source theorem.

## Statement proved

For an arbitrary commutative ring `R` and arbitrary type of variables `τ`,
if `(1 : ℕ∞) ≤ f.order`, then `(n : ℕ∞) ≤ (f ^ n).order` for every natural
`n`, including zero. Here `MvPowerSeries.order : MvPowerSeries τ R → ℕ∞`
is Mathlib's least total degree of a nonzero coefficient, with value `⊤`
for the zero series. No finiteness, decidability or domain hypothesis is
required. The exact theorem telescope is:

```lean
theorem d006
    {R : Type u} [CommRing R] {τ : Type v}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    d006Statement f n hf
```

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.natCast_le_order_pow_of_one_le_order_stabilization`: signature lines 205–209,
proof lines 210–213
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

The goal `d006Statement f n hf` is reducible to the source conclusion, so the
source `calc` applies directly: `(n : ℕ∞) = n • 1` (`nsmul_eq_mul`, `mul_one`),
`n • 1 ≤ n • f.order` (`nsmul_le_nsmul_right hf n`) and
`n • f.order ≤ (f ^ n).order` (`MvPowerSeries.le_order_pow n`).

## Changes from the source proof

The source proof body is used verbatim; the reducible target needs no
explicit unfolding. The source-private theorem in namespace
`LubinTate.SameUniformizer` becomes the public theorem
`Langlands.NYLL.PortInternal.M351.d006`. The conclusion is written as the
published `d006Statement f n hf`, and the source's two independent `Type*`
universes are named `u` and `v`. Binder order and kinds are preserved.
Unused source section variables, the local `Classical.propDecidable`
instance and the `noncomputable section` are omitted. Worker 489 supplied
the initial shared Lean/Markdown draft; Worker 544 verified its source
correspondence, checked the declaration and refined the documentation.

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
