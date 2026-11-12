# Orders, lattices and coset indicators for scalar Tate theory

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It introduces no new
original-source assertion. Everything is derived from the Library's valuative
local-field interface and its published Haar scaling theorem. It works over an
arbitrary nonarchimedean local field `F`, in any characteristic.

## Normalization data

`Normalization F` packages the data that the target statement quantifies over:
the residue cardinality `q`, a uniformizer `ϖ` in the sense of
`IsUniformizingElement`, and an absolute value `abv` with `abv ϖ = q⁻¹` and
`abv x = 1` whenever `valuation F x = 1`. Every field is a hypothesis of
the target statement, so the proof can build this structure from those
hypotheses.

- `ord x` is the exponent `k` with `v(x) = v(ϖ)^k`. It exists by the
  uniformizer property and is unique because `k ↦ v(ϖ)^k` is strictly
  antitone (`zpow_strictAnti`). By convention, `ord 0 = 0`. The lemmas
  `ord_mul`, `ord_inv`, `ord_zpow_ϖ` and `ord_eq_zero_iff` are the usual
  rules.
- `abv_eq` proves `abv x = q^{-ord x}` for `x ≠ 0`. Write
  `x = (x ϖ^{-ord x}) ϖ^{ord x}`. The first factor is a valuation unit, so
  `abv` takes the value one on it.

## Lattices

`ball n` is the additive subgroup `ϖ^n O = {x | v(x) ≤ v(ϖ)^n}`. The module
proves the following:

- membership in terms of the order (`mem_ball_iff_ord`) and `ball 0 = O`;
- antitonicity in `n`, multiplicativity (`mul_mem_ball`) and the shift rule
  `a x ∈ ball (n + ord a) ↔ x ∈ ball n`;
- `ball n` is open, closed and compact. Compactness uses
  `IsNonarchimedeanLocalField.isCompact_closedBall`.
- the lattices form a neighbourhood basis of zero (`exists_ball_subset`);
- the fibres of `ord` on `Fˣ` are open, so `ord` is locally constant and
  continuous on the unit group (`continuous_ord_units`). The fibre of order
  `k` equals `ball k \ ball (k+1)`.
- `measure_ball`: for any additive Haar measure `ν`,
  `ν(ϖ^n O) = q^{-n} ν(O)`. This follows from the published
  `HarmonicAnalysis.generalScalarHaarScalingStatement` applied to `ϖ^{-n}`,
  whose `abv`-value is `q^n`.

## Coset indicators and induction

`indicatorSB` turns the indicator of a compact clopen set into a
`SchwartzBruhat` function. `cosetIndicator x0 n` is the indicator of the
coset `x0 + ϖ^n O`.

`exists_ball_invariant` shows that every Schwartz--Bruhat function `f` is
invariant under translation by some lattice `ball m`. Local constancy gives a
lattice at each point. Finitely many of the corresponding cosets cover the
compact support, and the deepest lattice among them works on the whole support.
Off the support, the argument uses translation by `-h`.

`exists_coset_expansion` writes `f` as the finite sum
`∑_{x0 ∈ S} f(x0) · 1_{x0 + ϖ^m O}`. Here `S` is a set of representatives of
the finitely many cosets of `ball m` that meet the support.
`schwartzBruhat_induction` turns this into an induction principle. A property
that holds for `0`, is stable under sums and complex scalar multiples, and holds
for every coset indicator holds for every Schwartz--Bruhat function.

## Provenance

Describing Schwartz--Bruhat functions on a nonarchimedean local field as finite
combinations of lattice-coset indicators is standard. These lemmas are internal
consequences of the Library's definitions of `SchwartzBruhat` (locally constant
with compact support) and of the valuation. They do not translate any specific
numbered statement in the literature. The sources for the target itself are
listed in `LocalTateConductorStatement.md`.
