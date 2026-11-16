# NYLL M351.001: total-degree truncation through degree `m` (proof)

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_leStatement`
as the theorem
`Langlands.NYLL.LubinTate.SameUniformizer.truncTotal_succ_eq_iff_coeff_eq_degree_le`:
for a commutative semiring `R`, a `Finite` variable type `τ`, power series
`H H' : MvPowerSeries τ R` and `m : ℕ`,
`H.truncTotal (m + 1) = H'.truncTotal (m + 1)` holds if and only if
`coeff d H = coeff d H'` for every exponent `d` with `d.degree ≤ m`.
The theorem has exactly the binders of the target
(`{R} [CommSemiring R] {τ} [Finite τ] {H H'} (m)`) and its type is
`truncTotal_succ_eq_iff_coeff_eq_degree_leStatement (H := H) (H' := H') m`.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`
(SHA-256 `2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`),
readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`;
registered sources `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

The proof is that of source lines 49–66 (statement 42–48), unchanged.

## Proof

`constructor` splits the `↔` of the target (an `abbrev`).

- (`→`) Given equal truncations `h` and `d` with `d.degree ≤ m`, so
  `d.degree < m + 1` (`Nat.lt_succ_iff`), Mathlib's
  `MvPowerSeries.coeff_truncTotal` identifies `coeff d H` with the `d`-th
  coefficient of `H.truncTotal (m + 1)`; rewriting with `h` and applying
  `coeff_truncTotal` to `H'` gives `coeff d H'`.
- (`←`) Given coefficient agreement `h`, polynomial extensionality reduces
  to a coefficient `d`. If `d.degree < m + 1`, both truncation
  coefficients are rewritten to `coeff d H` and `coeff d H'` by
  `coeff_truncTotal`, which agree by `h`. Otherwise both vanish by
  `MvPowerSeries.coeff_truncTotal_eq_zero`.

## Imports and adaptations

The only import is the published statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U001.Statement`,
which imports `Mathlib.RingTheory.MvPowerSeries.Trunc`. Adaptations: the
`Langlands.NYLL` namespace prefix; the theorem type is written as the
target; the source's `noncomputable section`, `open scoped BigOperators`,
`universe u v w` and `open LocalFieldTheory.DiscreteValuationField` are
omitted (unused); a modified-file notice and docstrings are added.
The original 2026 copyright, Apache-2.0 release line and author header are
preserved; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
