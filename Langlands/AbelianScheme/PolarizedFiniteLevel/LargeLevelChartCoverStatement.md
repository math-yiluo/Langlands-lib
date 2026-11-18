# Eventual open chart covers of ordinary polarized full-level moduli

`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelChartCoverStatement` is a
proposition definition. It is a statement target only; this module proves
nothing.

## The statement

For every `P : Prerequisites.{0}` and all natural numbers `g d` with `0 < g`
and `0 < d`, there is a natural number `N` with the following property. For
every level `n ≥ N` with `hn : 3 ≤ n` there are:
- an index type `ι : Type`;
- level bases `X : ι → LevelBase n`;
- natural transformations
  `a i : uliftYoneda.{1}.obj (X i) ⟶ moduliFunctor P g d n hd hn`,

such that every `a i` is an open chart (`LevelBase.IsOpenChart`) and the family
covers the functor (`LevelBase.IsOpenChartCover`). These two notions are defined
in the internal module `LevelBaseZariski`. Informally, the published ordinary
polarized full-level moduli functor is covered by open subfunctors that are each
represented by a locally noetherian scheme on which `n` is a unit.

The quantifier pattern `∃ N, ∀ n ≥ N, ∀ hn : 3 ≤ n` and the hypotheses
`0 < g`, `0 < d` are those of the published target
`LargeLevelRepresentabilityStatement`.

## Provenance and role

This is a derived intermediate statement. The published target asserts that
the functor is represented by a level base `X`. The one chart `𝟙` from the
functor of points of `X` is then an open chart cover. So the target implies
this statement, and the statement holds by Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, Theorem 7.9 (printed p.139, PDF p.152 of the
registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).

The intended proof does not go through Theorem 7.9. It uses charts indexed by
tuples `ρ` of level indices. The chart for `ρ` is the open subfunctor where the
images of the torsion points `P_ρ` under the cubic embedding form a projective
frame of the cubic direct image of rank `6^g·d`. Frame normalization identifies
the embedding with a closed subscheme of a fixed projective space, so the chart
is represented by a locally closed subscheme of a Hilbert scheme times a
product of projective spaces. This follows GIT §7.2: Definition 7.5,
Proposition 7.3 and its proof (printed pp.130–134, PDF pp.143–147). The charts
cover the functor for large `n` because the `n`-torsion points of the fibres do
not concentrate on hyperplanes (the published `CubicTorsionHyperplaneBound`).

With `LevelBaseOpenChartGluingStatement` and `ModuliZariskiSheafStatement`,
this statement gives a representing level base. The published target also
needs `LargeLevelQuasiProjectivityStatement`.
