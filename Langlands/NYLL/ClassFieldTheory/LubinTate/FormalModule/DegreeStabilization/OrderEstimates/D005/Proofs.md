# NYLL M351.005: proof of the order of a monomial

The paired module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.D005.Proofs` proves the published target
`Langlands.NYLL.PortInternal.M351.d005Statement` (module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements`)
as the theorem `Langlands.NYLL.PortInternal.M351.d005`, with universe
parameters `u, v`. The theorem takes the source binders of M351.005 in
source order and kinds, and its type is `d005Statement d c`. Hence it is used exactly like the
source theorem.

## Statement proved

For an arbitrary commutative ring `R`, variable type `τ`, exponent
`d : τ →₀ ℕ` and coefficient `c : R`, the monomial `c X^d` has order at
least its total degree:

```lean
theorem d005
    {R : Type u} [CommRing R] {τ : Type v}
    (d : τ →₀ ℕ) (c : R) :
    d005Statement d c
```

The target expands to `(d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order`.
The coefficient may be zero, and `τ` need not be finite. The two universes
are independent.

## Source correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`, SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`, private
theorem `LubinTate.SameUniformizer.degree_le_order_monomial_stabilization`: signature lines 196–199,
proof lines 200–203
([pinned source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean>)). Registered sources:
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

## Implemented proof

After `unfold d005Statement` the goal is the source conclusion. With classical
decidability, split on `c = 0`. If `c = 0`, `simp` rewrites the monomial to `0`,
whose order is `⊤`, and closes the goal. Otherwise
`MvPowerSeries.order_monomial_of_ne_zero` rewrites the order to `d.degree`, and
the goal closes by reflexivity of `≤` after the rewrite.

## Changes from the source proof

The source proof is used verbatim after the added `unfold d005Statement`.
The private source name becomes the public name
`Langlands.NYLL.PortInternal.M351.d005`, and the source `Type*` binders are
named with independent universes `u` and `v`. Unused local-field section
variables and the source module's surrounding declarations are omitted.
Worker 499 reused Worker 489's shared proof draft and refined this Markdown.
The published target and its imports are unchanged.

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
