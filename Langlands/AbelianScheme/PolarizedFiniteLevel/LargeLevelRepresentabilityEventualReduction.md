# Eventual fine representability from gluing, the eventual sheaf property, charts and quasi-projectivity

This internal module reduces the published target `LargeLevelRepresentabilityStatement`
to four named statements. It adds no mathematical assertion beyond that implication; the
four statements stay explicit hypotheses. It differs from the module
`LargeLevelRepresentabilityReduction` only in its sheaf hypothesis, which here is the
weaker eventual form `EventualModuliZariskiSheafStatement`.

## Results

`eventualModuliZariskiSheaf_of_moduliZariskiSheaf` is a theorem: the published
`ModuliZariskiSheafStatement` (the sheaf property for every `n ≥ 3`) implies
`EventualModuliZariskiSheafStatement`. The proof takes the bound `N = 0` and applies the
hypothesis at each level.

`largeLevelRepresentability_of_eventualSheaf` is a proved definition: a `def` whose type is
the proposition `LargeLevelRepresentabilityStatement`. It takes four hypotheses:
- `Hglue : LevelBaseOpenChartGluingStatement` (Stacks 01JJ on level bases);
- `Hsheaf : EventualModuliZariskiSheafStatement` (the moduli functor is a Zariski sheaf for
  all sufficiently large `n ≥ 3`);
- `Hchart : LargeLevelChartCoverStatement` (eventual open chart covers);
- `Hqp : LargeLevelQuasiProjectivityStatement` (eventual quasi-projectivity of every
  representing level base).

## Proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. `Hsheaf`, `Hchart` and `Hqp` give bounds `N₀`,
`N₁` and `N₂`; take `N = max N₀ (max N₁ N₂)`. For `n ≥ N` with `3 ≤ n`:
1. `Hchart` gives an open chart cover `a` of the moduli functor by level bases `X i`.
2. `Hsheaf` gives the Zariski sheaf property of the moduli functor at level `n`.
3. `Hglue`, applied to steps 1 and 2, gives a level base `Y` and a natural isomorphism `e`
   from its functor of points to the moduli functor.
4. `Hqp`, applied to `Y` and `e`, gives quasi-compactness of the canonical morphism
   `Y.toLocalizationSpec` and an immersion `i` into a projective space over `ℤ[1/n]` lying
   over it.

The target's witnesses are then `Y`, `π = Y.toLocalizationSpec`, `m`, `i` and `e`.

## Provenance

This is an internal derivation. It only combines the conclusions of the four statements,
which are documented in their own modules.
